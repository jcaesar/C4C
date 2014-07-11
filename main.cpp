#include <utility>
using std::swap; using std::move; using std::forward; using std::remove_reference;
#include <memory>
using std::unique_ptr;
#include <limits>
using std::numeric_limits;
#include <stdexcept>
using std::runtime_error;
#include <string>
using std::string; using std::to_string;
#include <unordered_map>
using std::unordered_map;
#include <list>
using std::list;
#include <vector>
using std::vector;
#include <type_traits>
using std::underlying_type;
#include <cassert>
#include <iostream>

#include <llvm/Analysis/Passes.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Module.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/PassManager.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Transforms/Scalar.h>
using llvm::Module; using llvm::BasicBlock; using llvm::IRBuilder; using llvm::getGlobalContext; using llvm::Value; using llvm::FunctionType; using llvm::ExecutionEngine; using llvm::EngineBuilder; using llvm::FunctionPassManager; using llvm::APInt; using llvm::ConstantInt; using llvm::ConstantStruct; using llvm::AllocaInst; using llvm::StructType; using llvm::Constant; using llvm::CmpInst; using llvm::PHINode;
typedef llvm::Function llvmFunction;
typedef llvm::Type llvmType;

template<typename Res, typename... Args> std::unique_ptr<Res> make_unique(Args && ..._args) {
	return std::unique_ptr<Res>(new Res(std::forward<Args>(_args)...));
}
template <typename T, typename Pred>
auto map_vector(const T &vec, Pred f)
	-> std::vector<typename std::result_of<Pred(typename T::value_type)>::type>
{
	using ret_t = typename std::result_of<Pred(typename T::value_type)>::type; 
	std::vector<ret_t> ret;
	ret.reserve(vec.size());
	for(auto it = vec.begin(); it != vec.end(); ++it)
		ret.push_back(f(*it));
	return ret;
}



enum class Type : uint8_t {
	Nil = 0,
	Variant = 255,
	Integer = 1,
	Bool = 2,
};
underlying_type<Type>::type TypeTag(Type type) { return static_cast<std::underlying_type<Type>::type>(type); }
string Typename(Type type) {
	switch(type) {
		case Type::Nil: return "Nil/Void";
		case Type::Variant: return "Variant";
		case Type::Integer: return "Integer";
		case Type::Bool: return "Bool";
	}
}
/* For quick C&P
switch(type) {
	case Type::Nil: 
	case Type::Variant: 
	case Type::Integer: 
	case Type::Bool: 
}
*/
template<typename T> Type Type2Script();
template<> Type Type2Script<int32_t>() { return Type::Integer; }
template<> Type Type2Script<bool>()    { return Type::Bool; }
template<> Type Type2Script<void>()    { return Type::Nil; }


class CompilerError : public runtime_error { public: CompilerError(string msg) : runtime_error(msg) {} };
class UnknownIdentifier : public CompilerError { public: UnknownIdentifier(const string& identifier) : CompilerError("Unknown identifier " + identifier) {} };
class TypeConversion : public CompilerError { public: TypeConversion(Type from, Type to) : CompilerError("Cannot convert " + Typename(from) + " to " + Typename(to)) {} };
class CompilerInternal : public CompilerError { public: CompilerInternal(const string& msg) : CompilerError(msg) {} };
class Unreachable : public CompilerInternal { public: Unreachable() : CompilerInternal("Reached location presumed as unreachable.") {} };

class NamingProvider {
	private:
		string basename;
		static unordered_map<string, size_t> names;
		string make_name(string name) {
			auto it = names.find(name);
			if(it != names.end()) {
				return name + "." + to_string(++it->second);
			} else {
				names.emplace(name, 1);
				return name + ".1";
			}
		}
	public:
		NamingProvider(const string& basename) : basename(basename) {}
		string tmp(string hint) { return make_name(basename + ".tmp." + hint); }
		string block(string hint) { return make_name(basename + ".block." + hint); }
		string stack(string hint) { return make_name(basename + ".stack." + hint); }
		string tcv(string hint) { return make_name(basename + ".typeconversion." + hint); }
};
decltype(NamingProvider::names) NamingProvider::names;

class Function;
class Variable;
class Scope {
	private:
		Scope* parent = nullptr;
		unordered_map<string, unique_ptr<Function>> fns;
		unordered_map<string, Variable*> vars;
		template<typename T, typename Q>
		T& lookup(Q map, const string& name) {
			const auto it = (this->*map).find(name);
			if(it == (this->*map).end()) {
				if(parent)
					return parent->lookup<T, Q>(map, move(name));
				else
					throw UnknownIdentifier(name);
			} else
				return *it->second;
		}
	public:
		Scope() {}
		explicit Scope(Scope& parent) : parent(&parent) {}
		Function& func(string&& name) { string temp = move(name); return lookup<Function>(&Scope::fns, temp); }
		Function& func(const string& name) { return lookup<Function>(&Scope::fns, name); }
		Variable& var(const string& name) { return lookup<Variable>(&Scope::vars, name); }
		void addfunc(unique_ptr<Function> f);
		void addvar(Variable*);
		void forallfunctions(std::function<void(Function&)> l) { if(parent) parent->forallfunctions(l); for(auto& f: fns) l(*f.second); }
};

class SuperContext {
	private:
		Module* mod; // owned by execution engine
		ExecutionEngine* executionengine;
		unique_ptr<FunctionPassManager> funcpassmgr;
		Scope globalscope;
	public:
		explicit SuperContext(Scope&& scope) : globalscope(scope) {
			llvm::InitializeNativeTarget();
			mod = new Module("mm", getGlobalContext());
			string err;
			executionengine = EngineBuilder(mod).setErrorStr(&err).create();
			if(!executionengine)
				throw CompilerInternal("Could not create Execution Engine: " + err);
			executionengine->DisableSymbolSearching();
			funcpassmgr = make_unique<FunctionPassManager>(mod);
			//mod->setDataLayout(executionengine->getDataLayout());
			//funcpassmgr->add(new llvm::DataLayoutPass(mod));
			funcpassmgr->add(llvm::createBasicAliasAnalysisPass());
			funcpassmgr->add(llvm::createInstructionCombiningPass());
			funcpassmgr->add(llvm::createReassociatePass());
			funcpassmgr->add(llvm::createGVNPass());
			funcpassmgr->add(llvm::createCFGSimplificationPass());
			funcpassmgr->doInitialization();
			executionengine->addModule(mod);
		}
		SuperContext(SuperContext&&) = default;
		Scope& scope() { return globalscope; }
		Module& module() { assert(mod); return *mod; }
		ExecutionEngine& ee() { assert(executionengine); return *executionengine; }
		FunctionPassManager& fpm() { assert(funcpassmgr); return *funcpassmgr; }
};

class CompilationContext {
	private:
		SuperContext& supercontext;
		IRBuilder<> m_builder;
		NamingProvider m_names;
		Function& function;
		Scope contextscope;
	public:
		CompilationContext(SuperContext& sc, const string& name, Function& func) :
			supercontext(sc),
			m_builder(getGlobalContext()),
			m_names(name),
			function(func),
			contextscope(sc.scope())
		{
			llvmFunction* f = sc.module().getFunction(name);
			if(!f)
				throw CompilerInternal("Context for nonexistent function");
			BasicBlock* bb = BasicBlock::Create(getGlobalContext(), names().block("entry"), f);
			m_builder.SetInsertPoint(bb);
		}
		/*CompilationContext(CompilationContext& parent, const string& name) :
			m_module(parent.module()),
			m_builder(parent.builder()),
			m_names(parent.names().block(name)),
			m_scope(parent.scope()),
			function(parent.function)
		{
			builder().SetInsertPoint(&bb());
		}*/
		CompilationContext(const CompilationContext&) = delete;
		Module& module() { return supercontext.module(); }
		IRBuilder<>& builder() { return m_builder; }
		NamingProvider& names() { return m_names; }
		Scope& scope() { return contextscope; }
		Function& func() { return function; }
};

template<typename T>
T* checkCompile(T* t) {
	if(!t)
		throw CompilerInternal("Empty llvm result");
	return t;
}

class Statement {
	public:
		virtual ~Statement() {}
		virtual void compile(CompilationContext&) = 0;
};

size_t getVariantTypeSize() { return sizeof(Type)  * CHAR_BIT; }
size_t getVariantVarSize() { return sizeof(void*)  * CHAR_BIT; }
llvmType* getVariantTypeLLVMType() { return llvmType::getIntNTy(getGlobalContext(), getVariantTypeSize()); }
llvmType* getVariantVarLLVMType() {	return llvmType::getIntNTy(getGlobalContext(), getVariantVarSize()); }
StructType* getVariantLLVMType() { return StructType::get(getGlobalContext(), { getVariantTypeLLVMType(), getVariantVarLLVMType() }, false); }
llvmType* getLLVMType(Type type) {
	switch(type) {
		case Type::Nil: return llvmType::getVoidTy(getGlobalContext()); // I don't need space to save a Nil if I already know it's one at Compiletime
		case Type::Integer: return llvmType::getInt32Ty(getGlobalContext());
		case Type::Bool: return llvmType::getInt1Ty(getGlobalContext());
		case Type::Variant:	return getVariantLLVMType();
	}
}
Constant* TypeTagValue(Type type) {
	return checkCompile(ConstantInt::get(getGlobalContext(), APInt(getVariantTypeSize(), TypeTag(type), false)));
}

Value* defaultVariant(Type type) {
	return ConstantStruct::get(getVariantLLVMType(), vector<Constant*>{
		TypeTagValue(type),
		ConstantInt::get(getGlobalContext(), APInt(getVariantVarSize(), 0, false)),
	});
}
Value* defaultvalue(Type type) {
	switch(type) {
		case Type::Integer: return ConstantInt::get(getGlobalContext(), APInt(32, 0, true));
		case Type::Bool: return ConstantInt::get(getGlobalContext(), APInt(1, 0, false));
		case Type::Nil: case Type::Variant: return defaultVariant(Type::Nil);
	}
}

class RValue {
	private:
		static llvmFunction* variantconversionexternalfunc;
	public:
		static void prepare(SuperContext& sc) {
			variantconversionexternalfunc = checkCompile(llvmFunction::Create(FunctionType::get(getVariantVarLLVMType(), { getVariantTypeLLVMType(), getVariantTypeLLVMType(), getVariantVarLLVMType() }, false), llvmFunction::ExternalLinkage, "varianttypecoersion", &sc.module()));
			sc.ee().addGlobalMapping(variantconversionexternalfunc, (void*)&RValue::VariantCoersionFunction);
		}
	public:
		const Type type;
		Value * const value;
		RValue(Type type, Value* value) : type(type), value(checkCompile(value)) {}
		RValue convert(CompilationContext& cc, Type newtype);
		static void* VariantCoersionFunction(Type oldtype, Type newtype, void* val) {
			if(oldtype == Type::Integer && newtype == Type::Bool) {
				if(val != nullptr)
					return static_cast<char*>(nullptr)+1;
				else
					return nullptr;
			}
			if(oldtype == Type::Bool && newtype == Type::Integer) {
				if(val != nullptr)
					return static_cast<char*>(nullptr)+1;
				else
					return nullptr;
			}
			throw runtime_error("Cannot convert " + Typename(oldtype) + " to " + Typename(newtype) + "."); 
		}
};
decltype(RValue::variantconversionexternalfunc) RValue::variantconversionexternalfunc(nullptr);

class Variable : public Statement {
	protected:
		AllocaInst* stackptr = nullptr;
	public:
		const Type type;
		const string name;
		Variable(Type type, const string&& name) : type(type), name(move(name)) {
			if(type == Type::Nil)
				throw CompilerInternal("Variable with static type Nil");
		}
		void compile(CompilationContext& cc, Value* defaultvalue) {
			llvmFunction* f = cc.builder().GetInsertBlock()->getParent();
			IRBuilder<> entrybuilder(&f->getEntryBlock(), f->getEntryBlock().begin());
			stackptr = entrybuilder.CreateAlloca(getLLVMType(type), 0, cc.names().stack(name));
			if(!defaultvalue)
				defaultvalue = ::defaultvalue(type);
			store(cc, RValue(type, defaultvalue));
			cc.scope().addvar(this);
		}
		void compile(CompilationContext& cc) { compile(cc, nullptr); }
		RValue load(CompilationContext& cc) {
			if(!stackptr)
				throw CompilerInternal("Variable::load before Variable::compile");
			return RValue(type, cc.builder().CreateLoad(stackptr, cc.names().tmp(name)));
		}
		virtual void store(CompilationContext& cc, RValue&& value) {
			if(!stackptr)
				throw CompilerInternal("Variable::store before Variable::compile");
			cc.builder().CreateStore(value.convert(cc, type).value, stackptr);
		}
};

class Body {
	private:
		vector<unique_ptr<Statement>> body;
	public:
		Body() {}
		Body(vector<unique_ptr<Statement>>&& stmts) : body(move(stmts)) {}
		void add_statement(unique_ptr<Statement> stmt) { body.push_back(move(stmt)); }
		void compile(CompilationContext& cc);
};

class Function {
	protected:
		llvmFunction* f = nullptr;
	public:
		const string name;
		const Type returntype;
		Function(const string& fname, Type ret) : name(fname), returntype(ret) {}
		virtual ~Function() {};
		virtual void precompile(Module& m) {
			if(m.getFunction(name))
				throw CompilerInternal("Function has already been precompiled");
			FunctionType *ft = FunctionType::get(getLLVMType(returntype), map_vector(partypes(), getLLVMType), false);
			f = checkCompile(llvmFunction::Create(ft, llvmFunction::ExternalLinkage, name, &m));
			if (f->getName() != name) {
				f->eraseFromParent();
				throw CompilerInternal("Uncaught naming clash");
			}
		}
		virtual void compile(SuperContext& sc) = 0;
		llvmFunction& func() { if(!f) throw CompilerInternal("Reference to uncompiled function"); return *f; }
		virtual vector<Type> partypes() = 0;
		virtual RValue compilecall(CompilationContext& cc, vector<RValue> argvs) {
			return RValue(returntype, cc.builder().CreateCall(&func(),
				map_vector(argvs, [](const RValue& v){ return v.value; }),
				returntype != Type::Nil ? cc.names().tmp("call." + name) : ""));
		}
};

class ScriptFunction : public Function {
	private:
		Body body;
		vector<Variable> args;
	public:
		ScriptFunction(const string& name, Type ret, const vector<Variable>&& args, Body&& body) : Function(name, ret), body(move(body)), args(move(args)) {}
		virtual void precompile(Module& m) {
			Function::precompile(m);
			size_t i = 0;
			for (llvmFunction::arg_iterator argit = f->arg_begin(); i != args.size(); ++argit, ++i) {
				argit->setName(args[i].name);
			}
		}
		void compile(SuperContext& sc) {
			if(!f)
				throw CompilerInternal("Function::compile before Function::precompile");
			CompilationContext cc(sc, name, *this);
			llvmFunction::arg_iterator argit = f->arg_begin();
			for (unsigned i = 0; i != args.size(); ++i, ++argit) {
				args[i].compile(cc, argit);
			}
			assert(argit == f->arg_end());
			body.compile(cc);
			if(!cc.builder().GetInsertBlock()->getTerminator())
				cc.builder().CreateRet(cc.func().returntype == Type::Nil ? nullptr : defaultvalue(cc.func().returntype));
			f->dump();
			llvm::verifyFunction(*f);
			sc.fpm().run(*f);
		}
		vector<Type> partypes() { return map_vector(args, std::function<Type(const Variable&)>([](const Variable& arg){ return arg.type; })); }
};

class EngineFunction : public Function{
	private:
		void *ef = nullptr;
		vector<Type> argts;
	public:
		template<typename Result, typename... Args>
		EngineFunction(const string& name, Result(*func)(Args...)) : Function(name, Type2Script<Result>()), ef(reinterpret_cast<void*>(func)), argts{Type2Script<Args>()...} {}
		void compile(SuperContext& sc) {
			if(!f)
				throw CompilerInternal("Function::compile before Function::precompile");
			sc.ee().addGlobalMapping(f, ef);
		}
		vector<Type> partypes() { return argts; }
};

class Program {
	private:
		vector<unique_ptr<Function>> fns;
	public:
		void addfunc(unique_ptr<Function> fp) { fns.push_back(move(fp)); }
		SuperContext&& compile() {
			Scope globalscope;
			for(auto& fn: fns)
				globalscope.addfunc(move(fn));
			SuperContext sc(move(globalscope));
			
			RValue::prepare(sc);

			globalscope.forallfunctions([&sc](Function& f) { f.precompile(sc.module()); });
			globalscope.forallfunctions([&sc](Function& f) { f.compile(sc); });
			sc.module().MaterializeAllPermanently();
			
			return move(sc);
		}
};

class Expression {
	public:
		virtual ~Expression() {}
		virtual RValue compile(CompilationContext&) = 0;
};
typedef unique_ptr<Expression> Eup;

class Return : public Statement {
	private:
		Eup rv;
	public:
		Return(Eup rv) : rv(move(rv)) {}
		void compile(CompilationContext& cc) {
			if(cc.func().returntype == Type::Nil) {
				if(!rv)
					checkCompile(cc.builder().CreateRet(nullptr));
				else
					throw TypeConversion(rv->compile(cc).type, Type::Nil);
			} else {
				if(rv)
					checkCompile(cc.builder().CreateRet(rv->compile(cc).convert(cc, Type::Integer).value));
				else
					throw TypeConversion(Type::Nil, cc.func().returntype);
			}
		}
};

class Eval : public Statement {
	private:
		Eup ev;
	public:
		Eval(Eup ev) : ev(move(ev)) {}
		void compile(CompilationContext& cc) {
			checkCompile(ev->compile(cc).value);
		}
};

class Var : public Expression {
	private:
		string v;
	public:
		explicit Var(const string& v) : v(v) {}
		RValue compile(CompilationContext& cc) {
			return cc.scope().var(string(v)).load(cc);
		}
};

class ConstInt : public Expression {
	private:
		int32_t c;
	public:
		ConstInt(int32_t c) : c(c) {}
		RValue compile(CompilationContext& cc) {
			return RValue(Type::Integer, ConstantInt::get(getGlobalContext(), APInt(sizeof(c)*CHAR_BIT,c,numeric_limits<decltype(c)>::min < 0)));
		}
};

template<Type type, Type rettype>
class Binary : public Expression { // Currently integer binary
	protected:
		Eup lh, rh;
	private:
		virtual Value* compileInstr(CompilationContext& cc, Value* lhv, Value* rhv) = 0;
	public:
		Binary(Eup lh, Eup rh) : lh(move(lh)), rh(move(rh)) {}
		RValue compile(CompilationContext& cc) {
			auto lhv = lh->compile(cc).convert(cc, type);
			auto rhv = rh->compile(cc).convert(cc, type);
			return RValue(rettype, compileInstr(cc, lhv.value, rhv.value));
		}
};
class Plus  : public Binary<Type::Integer, Type::Integer> { public: using Binary::Binary; private: Value* compileInstr(CompilationContext& cc, Value* lhv, Value* rhv) { return cc.builder().CreateAdd(lhv, rhv, cc.names().tmp("add")); } };
class Minus : public Binary<Type::Integer, Type::Integer> { public: using Binary::Binary; private: Value* compileInstr(CompilationContext& cc, Value* lhv, Value* rhv) { return cc.builder().CreateSub(lhv, rhv, cc.names().tmp("sub")); } };
template<llvm::CmpInst::Predicate pdc>
class IntComparison : public Binary<Type::Integer, Type::Bool> {
	public: using Binary::Binary; 
	private: 
		Value* compileInstr(CompilationContext& cc, Value* lhv, Value* rhv) {
			return cc.builder().CreateICmp(pdc, lhv, rhv, cc.names().tmp(name())); 
		}
		virtual string name() = 0;
};

class Less      : public IntComparison<CmpInst::ICMP_SLT> { public: using IntComparison::IntComparison; string name() { return "less"     ; } };
class Greater   : public IntComparison<CmpInst::ICMP_SGT> { public: using IntComparison::IntComparison; string name() { return "greater"  ; } };
class LessEq    : public IntComparison<CmpInst::ICMP_SLE> { public: using IntComparison::IntComparison; string name() { return "lesseq"   ; } };
class GreaterEq : public IntComparison<CmpInst::ICMP_SGE> { public: using IntComparison::IntComparison; string name() { return "greatereq"; } };

class Assignment : public Expression { // Theoretically a binary operation, but technically too different
	private:
		string to;
		Eup rh;
	public:
		Assignment(const string& to, Eup rh) : to(to), rh(move(rh)) {}
		RValue compile(CompilationContext& cc) {
			Variable& var = cc.scope().var(to);
			RValue rhv = rh->compile(cc).convert(cc, var.type);
			var.store(cc, RValue(rhv));
			return rhv;
		}
};

class Call : public Expression {
	private:
		string fn;
		vector<Eup> args;
	public:
		Call(const string& fn, vector<Eup>&& args) : fn(fn), args(move(args)) {}
		RValue compile(CompilationContext& cc) {
			Function& callee = cc.scope().func(fn);
			auto partypes = callee.partypes();
			if (partypes.size() != args.size())
				throw CompilerError("Incorrect number of arguments passed: " + callee.name + " expects " + to_string(partypes.size()) + ", " + to_string(args.size()) + " given.");
			std::vector<RValue> argvs;
			for (unsigned i = 0, e = args.size(); i != e; ++i) {
				argvs.push_back(args[i]->compile(cc).convert(cc, partypes[i]));
			}
			return callee.compilecall(cc, argvs);
		}
};

class If : public Statement {
	private:
		Eup condition;
		Body thenbody;
		Body elsebody;
	public:
		If(Eup condition, Body thenbody, Body elsebody) : condition(move(condition)), thenbody(move(thenbody)), elsebody(move(elsebody)) {}
		void compile(CompilationContext& cc) {
			RValue ifcond(condition->compile(cc).convert(cc, Type::Bool));
			BasicBlock* orig = cc.builder().GetInsertBlock();

			BasicBlock* thenbb = BasicBlock::Create(getGlobalContext(), cc.names().block("if.then"), &cc.func().func());
			cc.builder().SetInsertPoint(thenbb);
			thenbody.compile(cc);
			BasicBlock* elsebb = BasicBlock::Create(getGlobalContext(), cc.names().block("if.else"), &cc.func().func());
			cc.builder().SetInsertPoint(elsebb);
			elsebody.compile(cc);

			cc.builder().SetInsertPoint(orig);
			cc.builder().CreateCondBr(ifcond.value, thenbb, elsebb);
			BasicBlock* continuation = BasicBlock::Create(getGlobalContext(), cc.names().block("if.continuation"), &cc.func().func());
			if(!thenbb->getTerminator()) {
				cc.builder().SetInsertPoint(thenbb);
				cc.builder().CreateBr(continuation);
			}
			if(!elsebb->getTerminator()) {
				cc.builder().SetInsertPoint(elsebb);
				cc.builder().CreateBr(continuation);
			}

			cc.builder().SetInsertPoint(continuation);
		}
};

class While : public Statement {
	private:
		Eup condition;
		Body body;
	public:
		While(Eup condition, Body body) : condition(move(condition)), body(move(body)) {}
		void compile(CompilationContext& cc) {

			// Blocks
			BasicBlock* orig = cc.builder().GetInsertBlock();
			BasicBlock* condbb = BasicBlock::Create(getGlobalContext(), cc.names().block("while.cond"), &cc.func().func());
			BasicBlock* bodybb = BasicBlock::Create(getGlobalContext(), cc.names().block("while.body"), &cc.func().func());
			BasicBlock* contbb = BasicBlock::Create(getGlobalContext(), cc.names().block("while.continuation"), &cc.func().func());

			// Compile
			cc.builder().CreateBr(condbb);

			cc.builder().SetInsertPoint(condbb);
			RValue whilecond(condition->compile(cc).convert(cc, Type::Bool));
			cc.builder().CreateCondBr(whilecond.value, bodybb, contbb);

			cc.builder().SetInsertPoint(bodybb);
			body.compile(cc);
			cc.builder().CreateBr(condbb);

			cc.builder().SetInsertPoint(contbb);
		}
};

namespace demo { // convenience functions for demonstration purposes - ugly to write, beautiful when used
	template<typename T, typename... Args> unique_ptr<Expression> e(Args && ... args) { return make_unique<T>(forward<Args>(args)...); }
	template<typename T, typename... Args> unique_ptr<Statement>  s(Args && ... args) { return make_unique<T>(forward<Args>(args)...); }
	template<typename T, typename... Args> unique_ptr<Function>   f(Args && ... args) { return make_unique<T>(forward<Args>(args)...); }

	template<typename L>
	void L_ins(vector<unique_ptr<L>>&) {}
	template<typename L, typename T1, typename... TR>
	void L_ins(vector<unique_ptr<L>>& v, T1 t1, TR... rest) {
		v.emplace_back(move(t1));
		L_ins(v, move(rest)...);
	}

	template<typename... T>	vector<unique_ptr<Statement>>  SL(T... t) { vector<unique_ptr<Statement>>  sl; L_ins<Statement> (sl, move(t)...); return move(sl); }
	template<typename... T>	vector<unique_ptr<Expression>> EL(T... t) { vector<unique_ptr<Expression>> el; L_ins<Expression>(el, move(t)...); return move(el); }

	int maindo(SuperContext&& sc) {
		sc.module().dump();
		auto mainf = sc.module().getFunction("Main");
		if(!mainf)
			throw CompilerError("No Main");
		auto scriptmain = reinterpret_cast<int32_t(*)()>(sc.ee().getPointerToFunction(mainf));
		if(!scriptmain)
			throw CompilerError("Nothing compiled");
		return (*scriptmain)();
	}
}

extern "C" {
void LogInt(int32_t i) {
	std::cout << i << std::endl;
}
void LogBool(bool f) {
	std::cout << (f?"true":"false") << std::endl;
}
}

int main() {
	using namespace demo;
	Program p;
	//p.addfunc(unique_ptr<ScriptFunction>(new ScriptFunction("Simpleton", Type::Nil, {}, Body(SL(s<Return>(nullptr))))));
	p.addfunc(unique_ptr<ScriptFunction>(new ScriptFunction("Foo", Type::Integer, { Variable(Type::Integer, "a"), Variable(Type::Integer, "b") }, Body(SL(s<Return>(e<Plus>(e<Plus>(e<Var>("a"), e<Var>("b")), e<ConstInt>(-1))))))));
	p.addfunc(unique_ptr<ScriptFunction>(new ScriptFunction("Bar", Type::Integer, { Variable(Type::Variant, "a"), Variable(Type::Variant, "b") }, Body(SL(
		s<Variable>(Type::Variant, "ret"),
		s<Eval>(e<Assignment>("ret", e<Call>("Foo", EL(e<Var>("a"), e<Var>("b"))))),
		s<If>(e<Less>(e<Var>("ret"), e<ConstInt>(3)), SL(s<Eval>(e<Assignment>("ret", e<ConstInt>(3)))), SL()),
		s<Return>(e<Var>("ret"))
	)))));
	p.addfunc(unique_ptr<ScriptFunction>(new ScriptFunction("Main", Type::Integer, {}, Body(SL(
		s<Eval>(e<Call>("LogInt", EL(e<Call>("Foo", EL(e<ConstInt>(1), e<ConstInt>(3)))))),
		s<Eval>(e<Call>("LogBool", EL(e<Call>("Foo", EL(e<ConstInt>(1), e<ConstInt>(2)))))),
		s<Eval>(e<Call>("LogBool", EL(e<ConstInt>(-2)))),
		s<Eval>(e<Call>("LogBool", EL(e<ConstInt>(-1)))),
		s<Eval>(e<Call>("LogBool", EL(e<ConstInt>( 0)))),
		s<Eval>(e<Call>("LogBool", EL(e<ConstInt>(+1)))),
		s<Eval>(e<Call>("LogBool", EL(e<ConstInt>(+2)))),
		s<Variable>(Type::Integer, "inttest"),
		s<Eval>(e<Assignment>("inttest", e<Call>("Foo", EL(e<ConstInt>(5), e<ConstInt>(2))))),
		s<Variable>(Type::Bool, "booltest"),
		s<Eval>(e<Assignment>("booltest", e<Var>("inttest"))),
		s<Eval>(e<Call>("LogBool", EL(e<Var>("booltest")))),
		s<Variable>(Type::Variant, "varianttest"),
		s<Eval>(e<Assignment>("varianttest", e<ConstInt>(13))),
		s<Eval>(e<Assignment>("varianttest", e<Var>("booltest"))),
		s<Eval>(e<Call>("LogBool", EL(e<Var>("varianttest")))),
		s<Eval>(e<Call>("VariantFuncTest", EL(e<ConstInt>(17)))),
		s<Eval>(e<Call>("WhileTest", EL(e<ConstInt>(7)))),
		s<Return>(e<ConstInt>(0))
	)))));
	p.addfunc(make_unique<EngineFunction>("LogInt", &LogInt));
	p.addfunc(make_unique<EngineFunction>("LogBool", &LogBool));
	p.addfunc(unique_ptr<ScriptFunction>(new ScriptFunction("VariantFuncTest", Type::Nil, { Variable(Type::Variant, "p") }, Body(SL(
		s<Eval>(e<Call>("LogInt", EL(e<Var>("p")))),
		s<Eval>(e<Call>("LogBool", EL(e<Var>("p"))))
	)))));
	p.addfunc(unique_ptr<ScriptFunction>(new ScriptFunction("WhileTest", Type::Nil, { Variable(Type::Integer, "upto") }, Body(SL(
		s<Variable>(Type::Variant, "i"),
		s<Eval>(e<Assignment>("i", e<ConstInt>(1))),
		s<While>(e<Less>(e<Var>("i"), e<Var>("upto")), SL(
			s<Eval>(e<Assignment>("i", e<Plus>(e<Var>("i"), e<ConstInt>(1)))),
			s<Eval>(e<Call>("LogInt", EL(e<Var>("i"))))
		))
	)))));
	//p.addfunc(unique_ptr<Function>(new ScriptFunction("LogInt", Type::Nil, {Variable(Type::Integer, "discard")}, Body(SL(s<Return>(nullptr))))));
	return maindo(move(p.compile()));
}

void Scope::addfunc(unique_ptr<Function> f) { if(parent) parent->addfunc(move(f)); else { string name = f->name; fns.emplace(name, move(f)); } }
void Scope::addvar(Variable* v) { string name = v->name; vars.emplace(name, v); }
RValue RValue::convert(CompilationContext& cc, Type newtype)
{
	if(newtype == type)
		return *this;
	if(newtype == Type::Variant) {
		Value* newvalue = nullptr;
		switch(type) {
			case Type::Nil: newvalue = defaultVariant(type); break;
			case Type::Integer:
			case Type::Bool: newvalue = cc.builder().CreateInsertValue(defaultVariant(type),
									 cc.builder().CreateZExt(value, getVariantVarLLVMType(), cc.names().tcv("intbooltovariantvalue")),
									 {1}, cc.names().tcv("intbooltovariant")); break;
			case Type::Variant: throw Unreachable();
		}
		return RValue(Type::Variant, newvalue);
	}
	if(type == Type::Variant) {
		switch(newtype) {
			case Type::Integer:	case Type::Bool: {
				Value* typetag = checkCompile(cc.builder().CreateExtractValue(value, {0}, cc.names().tcv("varianttointbool.typetag")));
				Value* typematch = checkCompile(cc.builder().CreateICmp(CmpInst::ICMP_EQ, TypeTagValue(newtype), typetag, cc.names().tcv("varianttointbool.typematch")));
				Value* extract = checkCompile(cc.builder().CreateExtractValue(value, {1}, cc.names().tcv("varianttointbool.directextract")));
				BasicBlock* orig = cc.builder().GetInsertBlock();
				BasicBlock* mismatch = BasicBlock::Create(getGlobalContext(), cc.names().block("varianttointbool.typemismatch"), &cc.func().func());
				BasicBlock* continuation = BasicBlock::Create(getGlobalContext(), cc.names().block("varianttointbool.continuation"), &cc.func().func());
				cc.builder().CreateCondBr(typematch, continuation, mismatch);
				cc.builder().SetInsertPoint(mismatch);
				if(!variantconversionexternalfunc) throw CompilerInternal("RValue was not prepare()d");
				Value* coersion = checkCompile(cc.builder().CreateCall(variantconversionexternalfunc, { typetag, TypeTagValue(newtype), extract }, cc.names().tcv("varianttoint.enginecoersion")));
				cc.builder().CreateBr(continuation);
				cc.builder().SetInsertPoint(continuation);
				PHINode *pn = cc.builder().CreatePHI(getVariantVarLLVMType(), 2, cc.names().tcv("varianttointbool.merge"));
				pn->addIncoming(extract, orig);
				pn->addIncoming(coersion, mismatch);
				Value* trunc = checkCompile(cc.builder().CreateTrunc(pn, getLLVMType(newtype), cc.names().tcv("varianttointbool.trunc")));
				return RValue(newtype, trunc);
			} break;
			case Type::Nil: case Type::Variant: throw Unreachable();
		}
	}
	if(newtype == Type::Bool && type == Type::Integer)
		return RValue(Type::Bool, cc.builder().CreateICmp(CmpInst::ICMP_NE, value, ConstInt(0).compile(cc).value, cc.names().tcv("inttobool")));
	throw TypeConversion(type, newtype);
}

void Body::compile(CompilationContext& cc) {
	for(auto& stmt: body) {
		stmt->compile(cc);
		if(cc.builder().GetInsertBlock()->getTerminator())
			return;
	}
}
