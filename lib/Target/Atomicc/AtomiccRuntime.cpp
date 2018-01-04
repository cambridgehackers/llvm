//===-- AtomiccRuntime.cpp - Generating Verilog from LLVM -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements zzz
//
//===----------------------------------------------------------------------===//
#include <cxxabi.h> // abi::__cxa_demangle
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

#include "AtomiccDecl.h"

static int trace_malloc;//= 1;
static int trace_fixup;//= 1;
int trace_pair;//= 1;

std::list<MEMORY_REGION> memoryRegion;

/*
 * Remove Alloca items inserted by clang as part of dwarf debug support.
 * (the 'this' pointer was copied into a stack temp rather than being
 * referenced directly from the parameter)
 * Context: Must be after processMethodToFunction
 */
static void processAlloca(Function *func)
{
    std::map<const Value *,Instruction *> remapValue;
restart:
    remapValue.clear();
    for (auto BB = func->begin(), BE = func->end(); BB != BE; ++BB) {
        for (auto IIb = BB->begin(), IE = BB->end(); IIb != IE;) {
            auto PI = std::next(BasicBlock::iterator(IIb));
            Instruction *II = &*IIb;
            switch (II->getOpcode()) {
            case Instruction::Store:
                if (Instruction *target = dyn_cast<Instruction>(II->getOperand(1))) {
                if (target->getOpcode() == Instruction::Alloca) {
                    if (!dyn_cast<CallInst>(II->getOperand(0))) { // don't do remapping for calls
                    // remember values stored in Alloca temps
                    remapValue[II->getOperand(1)] = II;
//printf("[%s:%d] STORE %p\n", __FUNCTION__, __LINE__, II);
                    }
                }
                }
                break;
            case Instruction::Load:
                if (Instruction *val = remapValue[II->getOperand(0)]) {
                    // replace loads from temp areas with stored values
//printf("[%s:%d] LOAD %p\n", __FUNCTION__, __LINE__, val);
                    II->replaceAllUsesWith(val->getOperand(0));
                    recursiveDelete(II);
                }
                break;
            case Instruction::Call: {
                CallInst *ICL = dyn_cast<CallInst>(II);
                Value *callV = ICL->getCalledValue();
                IRBuilder<> builder(II->getParent());
                builder.SetInsertPoint(II);
                if (ICL->getDereferenceableBytes(0) > 0) {
                    Value *newLoad = builder.CreateLoad(II->getOperand(1));
                    builder.CreateStore(newLoad, II->getOperand(0));
                    II->eraseFromParent();
                }
                else if (Function *cfunc = dyn_cast<Function>(callV)) {
                    int status;
                    std::string calledName = cfunc->getName();
                    const char *ret = abi::__cxa_demangle(calledName.c_str(), 0, 0, &status);
                    std::string temp;
                    if (ret)
                        temp = ret;
                    int colon = temp.find("::");
                    int lparen = temp.find("(");
                    if (calledName == "llvm.memcpy.p0i8.p0i8.i64") {
                    if (Instruction *dest = dyn_cast<Instruction>(II->getOperand(0)))
                    if (dest->getOpcode() == Instruction::BitCast)
                    if (Instruction *src = dyn_cast<Instruction>(II->getOperand(1)))
                    if (src->getOpcode() == Instruction::BitCast) {
                        builder.CreateStore(builder.CreateLoad(src->getOperand(0)),
                            dest->getOperand(0));
                        printf("[%s:%d] deleting call\n", __FUNCTION__, __LINE__);
                        recursiveDelete(II);
                        goto restart;
                    }
                    }
#if 1
    else if (calledName == "fixedGet") {
printf("[%s:%d]GET\n", __FUNCTION__, __LINE__);
II->getParent()->getParent()->dump();
II->dump();
II->getOperand(0)->dump();
        //II->replaceAllUsesWith(II->getOperand(0));
        II->eraseFromParent();
    }
    else if (calledName == "fixedSet") {
printf("[%s:%d]SET\n", __FUNCTION__, __LINE__);
II->dump();
        builder.CreateStore(II->getOperand(0), II->getOperand(1));
        II->eraseFromParent();
    }
#endif
                    else if (colon != -1 && lparen > colon) {
                        std::string classname = temp.substr(0, colon);
                        std::string fname = temp.substr(colon+2, lparen - colon - 2);
                        int lt = classname.find("<");
                        if (lt > 0)
                            classname = classname.substr(0,lt);
                        if (classname == fname) {
                            processAlloca(cfunc);
                            InlineFunctionInfo IFI;
                            InlineFunction(ICL, IFI);//, false);
                            goto restart;
                        }
                    }
                }
                break;
                }
            };
            IIb = PI;
        }
    }
    for (auto item: remapValue) {
        if (item.second)
        if (Instruction *allocItem = dyn_cast<Instruction>(item.second->getOperand(1))) {
            int count = 0;
            for (auto UB = allocItem->use_begin(), UE = allocItem->use_end(); UB != UE; UB++)
                 count++;
            if (count == 1)
                recursiveDelete(item.second);
        }
    }
}

/*
 * Lookup vtable-referenced functions, changing IR to reference actual bound
 * function directly.  Also inline references to methods from the same class,
 * since these internal references must be inlined in generated verilog.
 */
static void processMethodInlining(Function *thisFunc, Function *parentFunc)
{
restart: // restart here after inlining function.... basic block structure might change
    for (auto BB = thisFunc->begin(), BE = thisFunc->end(); BB != BE; ++BB) {
        for (auto II = BB->begin(), IE = BB->end(); II != IE;) {
            auto PI = std::next(BasicBlock::iterator(II));
            if (CallInst *ICL = dyn_cast<CallInst>(II)) {
                Module *Mod = thisFunc->getParent();
                std::string callingName = thisFunc->getName();
                const StructType *callingSTy = findThisArgument(thisFunc);
                Value *callV = ICL->getCalledValue();
                Function *func = dyn_cast<Function>(callV);
                if (Instruction *oldOp = dyn_cast<Instruction>(callV)) {
                    std::string opName = printOperand(callV, false);
                    func = dyn_cast_or_null<Function>(Mod->getNamedValue(opName));
                    if (!func) {
                        printf("%s: %s not an instantiable call!!!! %s\n", __FUNCTION__, parentFunc->getName().str().c_str(), opName.c_str());
                        II->dump();
                        thisFunc->dump();
                        callingSTy->dump();
                        if (parentFunc != thisFunc)
                            parentFunc->dump();
                        exit(-1);
                    }
                    II->setOperand(II->getNumOperands()-1, func);
                    recursiveDelete(oldOp);
                }
                std::string calledName = func->getName();
                const StructType *STy = findThisArgument(func);
                //printf("%s: %s CALLS %s cSTy %p STy %p parentFunc %p func %p thisFunc %p\n", __FUNCTION__, callingName.c_str(), calledName.c_str(), callingSTy, STy, parentFunc, func, thisFunc);
                if (parentFunc != func && thisFunc != func)
                if (callingSTy == STy || endswith(calledName, "C2Ev") || endswith(calledName, "D2Ev")) {
                    //fprintf(stdout,"callProcess: %s cName %s single!!!!\n", callingName.c_str(), calledName.c_str());
                    processAlloca(func);
                    processMethodInlining(func, parentFunc);
                    InlineFunctionInfo IFI;
//printf("[%s:%d] beforeInline thisFunc %p func %p\n", __FUNCTION__, __LINE__, thisFunc, func);
//thisFunc->dump();
//func->dump();
                    if (thisFunc != func)
                        InlineFunction(ICL, IFI);//, false);
                    goto restart;
                }
            };
            II = PI;
        }
    }
}

void setSeen(Function *func, std::string mName)
{
    //printf("[%s:%d] mname %s funcname %s\n", __FUNCTION__, __LINE__, mName.c_str(), func->getName().str().c_str());
    processAlloca(func);
    // inline intra-class method call bodies
    processMethodInlining(func, func);
}
/*
 * Add a function to the processing list for generation of cpp and verilog.
 */
static void pushWork(std::string mName, Function *func)
{
    assert (func);
    const StructType *STy = findThisArgument(func);
    ClassMethodTable *table = classCreate[STy];
    setSeen(func, mName);
    //printf("[%s:%d] setmethodddd %s = %p %s\n", __FUNCTION__, __LINE__, mName.c_str(), func, func->getName().str().c_str());
    table->method[mName] = func;
    // inline intra-class method call bodies
    processMethodInlining(func, func);
    fixupFuncList.push_back(func);
}

/*
 * Methods, guarded values, rules all get pushed as pairs so that 'RDY' function
 * is processed after processing for base method (so that guards promoted during
 * the method processing are later handled)
 */
static void pushPair(Function *enaFunc, std::string enaName, Function *rdyFunc, std::string rdyName)
{
    ruleRDYFunction[enaFunc] = rdyFunc; // must be before pushWork() calls
    ruleENAFunction[rdyFunc] = enaFunc;
    pushWork(enaName, enaFunc);
    pushWork(rdyName, rdyFunc); // must be after 'ENA', since hoisting copies guards
}

/*
 * Process 'blocks' functions that were generated for user rules.
 * The blocks context is removed; the functions are transformed into
 * a method (and its associated RDY method), attached to the containing class.
 */
extern "C" Function *fixupFunction(uint64_t *bcap, Function *argFunc)
{
    static int counter;
    ValueToValueMapTy VMap;
    SmallVector<ReturnInst*, 8> Returnsfunc;  // Ignore returns cloned.

    // first clone template function into temp function, so that we can
    // edit, filling in actual captured data values
    if (trace_fixup) {
        printf("[%s:%d] BEFORECLONE func %p\n", __FUNCTION__, __LINE__, argFunc);
        argFunc->dump();
    }
    PointerType *thisType = dyn_cast<PointerType>(argFunc->arg_begin()->getType());

    Type *Params[] = {thisType};
    Function *func = Function::Create(FunctionType::get(argFunc->getReturnType(),
        ArrayRef<Type*>(Params, 1), false), GlobalValue::LinkOnceODRLinkage,
        "ActualTargetFunction", argFunc->getParent());
    func->arg_begin()->setName("this");
    int argCount = 0;
    for (auto AI = argFunc->arg_begin(), AE = argFunc->arg_end();
         AI != AE; AI++, argCount++) {
        Argument *arg = AI;
        if (argCount < 1)
            VMap[arg] = func->arg_begin();
        else {
            int64_t val = bcap[argCount-1];
            printf("[%s:%d] Load %lld\n", __FUNCTION__, __LINE__, val);
            VMap[arg] = ConstantInt::get(arg->getType(), val);
        }
    }
    CloneFunctionInto(func, argFunc, VMap, false, Returnsfunc, "", nullptr);
    processAlloca(func);
    for (auto BB = func->begin(), BE = func->end(); BB != BE; ++BB) {
        for (auto IIb = BB->begin(), IE = BB->end(); IIb != IE; ) {
            BasicBlock::iterator PI = std::next(BasicBlock::iterator(IIb));
            Instruction *II = &*IIb;
            switch (II->getOpcode()) {
            case Instruction::SExt: {
                if (const ConstantInt *CI = dyn_cast<ConstantInt>(II->getOperand(0))) {
                    /* After inlining integers, we have some SExt references to constants
                     * (these are for the offset parameters to GEP instructions.
                     * Since the argument to SExt is just an integer, we can replace
                     * all references to the SExt with the integer value itself
                     * (using the datatype of the SExt).
                     */
                    IRBuilder<> builder(II->getParent());
                    builder.SetInsertPoint(II);
                    int64_t val = CI->getZExtValue();
                    printf("%s: SExt %ld\n", __FUNCTION__, val);
                    II->replaceAllUsesWith(ConstantInt::get(II->getType(), val));
                    recursiveDelete(II);
                }
                break;
                }
            }
            IIb = PI;
        }
    }
    if (trace_fixup) {
        printf("[%s:%d] AFTER\n", __FUNCTION__, __LINE__);
        func->dump();
    }
    return func;
}

/*
 * Functions called from user constructors during static initialization
 */

/*
 * Allocated memory region management
 */
extern "C" void *llvm_translate_malloc(size_t size, Type *type, const StructType *STy, uint64_t vecCount)
{
    size_t newsize = size * 2 + MAX_BASIC_BLOCK_FLAGS * sizeof(int) + GIANT_SIZE;
    void *ptr = malloc(newsize);
    memset(ptr, 0x5a, newsize);
    if (trace_malloc)
        printf("[%s:%d] %ld = %p type %p sty %p vecCount %lld\n", __FUNCTION__, __LINE__, size, ptr, type, STy, vecCount);
    memoryRegion.push_back(MEMORY_REGION{ptr, newsize, type, STy, vecCount});
    return ptr;
}

/*
 * Called from user constructors to process Blocks functions generated for a rule
 * Rules only support RDY/ENA signalling.
 */
extern "C" void addBaseRule(void *thisp, const char *name, Function *rdyFunc, Function *enaFunc)
{
    std::string enaName = name;
    ClassMethodTable *table = classCreate[findThisArgument(rdyFunc)];
    table->ruleFunctions[name] = enaFunc;
    if (trace_pair)
        printf("[%s:%d] name %s ena %s rdy %s\n", __FUNCTION__, __LINE__, name, enaFunc->getName().str().c_str(), rdyFunc->getName().str().c_str());
    pushPair(enaFunc, enaName + "__ENA", rdyFunc, enaName + "__RDY");
}

/*
 * Called from user constructors to set priority on a rule
 */
extern "C" void atomiccSchedulePriority(const char *rule, const char *priority, const StructType *STy)
{
    ClassMethodTable *table = classCreate[STy];
    printf("%s: %s %s %p\n", __FUNCTION__, rule, priority, STy);
    STy->dump();
    table->priority[rule] = priority;
}

/*
 * Called from user constructors to set interface methods
 */
typedef struct {
    std::string fname;
    Function   *func;
} FuncInfo;
static void replaceFunc(Function *target, Function *source)
{
    auto bb = target->begin();
    Instruction *TI = bb->getTerminator();
    if (source) {
        for (auto II = bb->begin(), IE = bb->end(); II != IE;II++)
            if (II->getOpcode() == Instruction::Call) {
                cast<CallInst>(&*II)->setCalledFunction(source);
                return;
            }
    }
    else if (TI->getOpcode() == Instruction::Ret) {
        IRBuilder<> builder(&*bb);
        builder.SetInsertPoint(TI);
        Value *oldI = TI->getOperand(0);
        Value *newI = builder.getInt1(1);
        if (oldI != newI) {
            oldI->replaceAllUsesWith(newI);
            recursiveDelete(oldI);
        }
    }
}
extern "C" void atomiccInterfaceName(const char *target, const char *source, const StructType *STy)
{
    ClassMethodTable *table = classCreate[STy];
    std::string enaName = target;
    std::string enaSuffix = "__ENA";
    //if (endswith(item.first, "__READY")) {
        //enaName = item.first.substr(0, item.first.length() - 7);
        //enaSuffix = "__VALID";
    //}
std::string rdyString = "__RDY";
printf("[%s:%d] target %s source %s STy %p table %p\n", __FUNCTION__, __LINE__, target, source, STy, table);
    std::map<std::string, FuncInfo> funcMap;
    int len = STy->structFieldMap.length();
    int subs = 0, last_subs = 0;
    while (subs < len) {
        while (subs < len && STy->structFieldMap[subs] != ',') {
            subs++;
        }
        subs++;
        if (STy->structFieldMap[last_subs] == '/')
            last_subs++;
        std::string ret = STy->structFieldMap.substr(last_subs);
        int idx = ret.find(',');
        if (idx >= 0)
            ret = ret.substr(0,idx);
        idx = ret.find(':');
        if (idx >= 0) {
            std::string fname = ret.substr(0, idx);
            Function *func = globalMod->getFunction(fname);
            std::string mName = ret.substr(idx+1);
            if (func)
                funcMap[mName] = {fname, func};
//printf("[%s:%d] fname %s mName %s func %p\n", __FUNCTION__, __LINE__, fname.c_str(), mName.c_str(), func);
            }
        last_subs = subs;
    }
    Function *enaFunc = funcMap[target].func;
    Function *rdyFunc = funcMap[target + rdyString].func;
    Function *senaFunc = funcMap[source].func;
    Function *srdyFunc = funcMap[source + rdyString].func;
printf("[%s:%d] functions: target %s / %s  source %s / %s\n", __FUNCTION__, __LINE__,
    funcMap[target].fname.c_str(), funcMap[target + rdyString].fname.c_str(),
    funcMap[source].fname.c_str(), funcMap[source + rdyString].fname.c_str());
printf(" functions: target %p / %p  source %p / %p\n", enaFunc, rdyFunc, senaFunc, srdyFunc);
    if (!enaFunc || !rdyFunc || !senaFunc) {
        printf("[%s:%d] %s function NULL %p rdy %p BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB \n", __FUNCTION__, __LINE__, enaName.c_str(), enaFunc, rdyFunc);
        return;
    }
    replaceFunc(enaFunc, senaFunc);
    replaceFunc(rdyFunc, srdyFunc);
    if (!isActionMethod(enaFunc))
        enaSuffix = "";
    std::string rdyName = enaName + rdyString;
    enaName += enaSuffix;
    table->method[enaName] = enaFunc;
    table->method[rdyName] = rdyFunc;
    pushPair(enaFunc, enaName, rdyFunc, rdyName);
//printf("[%s:%d] DDUMMMMMMMMMMMMP\n", __FUNCTION__, __LINE__);
//enaFunc->dump();
//rdyFunc->dump();
}
