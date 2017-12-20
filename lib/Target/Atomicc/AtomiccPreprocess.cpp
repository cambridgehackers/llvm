//===-- AtomiccPreprocess.cpp - Generating Verilog from LLVM -----===//
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
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/TypeFinder.h"

using namespace llvm;

#include "AtomiccDecl.h"

static void processSelect(Function *thisFunc)
{
    for (auto BB = thisFunc->begin(), BE = thisFunc->end(); BB != BE; ++BB) {
        for (auto IIb = BB->begin(), IE = BB->end(); IIb != IE;) {
            Instruction *II = &*IIb;
            auto PI = std::next(BasicBlock::iterator(II));
            switch (II->getOpcode()) {
            case Instruction::Select:
                // a Select instruction is generated for size calculation for
                // _Znam (operator new[](unsigned long))
                II->replaceAllUsesWith(II->getOperand(2));
                recursiveDelete(II);
                break;
            };
            IIb = PI;
        }
    }
}

static void processInterfaceName(CallInst *II)
{
    Function *callingFunction = II->getParent()->getParent();
    IRBuilder<> builder(II->getParent());
    builder.SetInsertPoint(II);
    const StructType *STy = findThisArgument(callingFunction);
    Value *oldOp = II->getOperand(2);
    II->setOperand(2, ConstantInt::get(Type::getInt64Ty(II->getContext()), (uint64_t)STy));
}

static void processConnectInterface(CallInst *II)
{
    if (Instruction *ins = dyn_cast<Instruction>(II->getOperand(0)))
    if (ins->getOpcode() == Instruction::BitCast)
    if (PointerType *PTy = dyn_cast<PointerType>(ins->getOperand(0)->getType()))
    if (StructType *STy = dyn_cast<StructType>(PTy->getElementType())) {
        getClass(STy);  // make sure that classCreate is initialized
        ClassMethodTable *table = classCreate[STy];
        std::string sname = STy->getName();
        std::string target = printOperand(II->getOperand(1), false);
        std::string source = printOperand(II->getOperand(2), false);
        int ind = target.find(".");
        if (ind > 0)
            target = target.substr(ind+1);
        ind = source.find(".");
        if (ind > 0)
            source = source.substr(ind+1);
        if (source[source.length() - 1] == '_') // weird postfix '_'!!
            source = source.substr(0, source.length()-1);
        if (Instruction *sins = dyn_cast<Instruction>(II->getOperand(2)))
        if (sins->getOpcode() == Instruction::BitCast)
        if (PointerType *iPTy = dyn_cast<PointerType>(sins->getOperand(0)->getType()))
        if (StructType *iSTy = dyn_cast<StructType>(iPTy->getElementType())) {
            std::string isname = iSTy->getName();
printf("[%s:%d] sname %s table %p source %s target %s isname %s\n", __FUNCTION__, __LINE__, sname.c_str(), table, source.c_str(), target.c_str(), isname.c_str());
        for (unsigned i = 0; i < II->getNumOperands()-1; i++)
             printf("arg[%d] = %s\n", i, printOperand(II->getOperand(i), false).c_str());
        table->interfaceConnect.push_back(InterfaceConnectType{target, source, iSTy});
        }
    }
    recursiveDelete(II);      // No longer need to call connectInterface() !
}

/*
 * Map calls to 'new()' and 'malloc()' in constructors to call 'llvm_translate_malloc'.
 * This enables llvm-translate to easily maintain a list of valid memory regions
 * during processing.
 */
Value *findElementCount(Instruction *I)
{
    Value *ret = NULL;
    if (I) {
        if (CallInst *CI = dyn_cast<CallInst>(I)) {
            if (Value *called = CI->getOperand(CI->getNumOperands()-1))
            if (const Function *CF = dyn_cast<Function>(called))
            if (CF->getName() == "_ZL20atomiccNewArrayCountm") {
printf("[%s:%d] FOUND\n", __FUNCTION__, __LINE__);
                return CI->getOperand(0);
            }
        }
        for (unsigned int i = 0; i < I->getNumOperands() && !ret; i++) {
            ret = findElementCount(dyn_cast<Instruction>(I->getOperand(i)));
        }
    }
    return ret;
}

static void processMSize(CallInst *II)
{
    II->replaceAllUsesWith(II->getOperand(0));
    II->eraseFromParent();
}

static void processMalloc(CallInst *II)
{
    //Function *callingFunc = II->getParent()->getParent();
    Module *Mod = II->getParent()->getParent()->getParent();
    Value *called = II->getOperand(II->getNumOperands()-1);
    const Function *CF = dyn_cast<Function>(called);
    const Type *Typ = NULL;
    const StructType *STy = findThisArgument(II->getParent()->getParent());
    uint64_t styparam = (uint64_t)STy;
    for(auto PI = II->user_begin(), PE = II->user_end(); PI != PE; PI++) {
        Instruction *ins = dyn_cast<Instruction>(*PI);
        //printf("[%s:%d] ins %p opcode %s\n", __FUNCTION__, __LINE__, ins, ins->getOpcodeName());
        //ins->dump();
        if (ins->getOpcode() == Instruction::BitCast) {
            if (!Typ)
                Typ = ins->getType();
        }
        if (ins->getOpcode() == Instruction::GetElementPtr) {
            Instruction *PI = ins->user_back();
            //PI->dump();
            if (PI->getOpcode() == Instruction::BitCast)
                Typ = PI->getType();
        }
    }
    Value *vecparam = NULL;
    if (CF->getName() == "_Znam")
        vecparam = findElementCount(II);
    uint64_t tparam = (uint64_t)Typ;
    //printf("%s: %s calling %s styparam %lx tparam %lx vecparam %p\n",
        //__FUNCTION__, callingFunc->getName().str().c_str(), CF->getName().str().c_str(), styparam, tparam, vecparam);
    //STy->dump();
    //if (Typ)
        //Typ->dump();
    //II->dump();
    Type *Params[] = {Type::getInt64Ty(Mod->getContext()),
        Type::getInt64Ty(Mod->getContext()), Type::getInt64Ty(Mod->getContext()),
        Type::getInt64Ty(Mod->getContext())};
    FunctionType *fty = FunctionType::get(Type::getInt8PtrTy(Mod->getContext()),
        ArrayRef<Type*>(Params, 4), false);
    Function *F = dyn_cast<Function>(Mod->getOrInsertFunction("llvm_translate_malloc", fty));
    F->setCallingConv(CF->getCallingConv());
    //F->setDoesNotAlias(0);
    F->setAttributes(CF->getAttributes());
    IRBuilder<> builder(II->getParent());
    builder.SetInsertPoint(II);
    if (!vecparam)
        vecparam = builder.getInt64(-1);
    II->replaceAllUsesWith(builder.CreateCall(F,
       {II->getOperand(0), builder.getInt64(tparam), builder.getInt64(styparam), vecparam},
       "llvm_translate_malloc"));
    II->eraseFromParent();
}

/*
 * In atomiccSchedulePriority calls, replace 3rd parameter with pointer
 * to StructType of calling class. (called from a constructor)
 */
static void processPriority(CallInst *II)
{
    II->setOperand(2, ConstantInt::get(II->getOperand(2)->getType(),
        (uint64_t)findThisArgument(II->getParent()->getParent())));
}

/*
 * replace unsupported calls to llvm.umul.with.overflow.i64, llvm.uadd.with.overflow.i64
 */
static void processOverflow(CallInst *II)
{
    Function *func = dyn_cast<Function>(II->getCalledValue());
    std::string fname = func->getName();
    IRBuilder<> builder(II->getParent());
    builder.SetInsertPoint(II);
    Value *LHS = II->getOperand(0);
    Value *RHS = II->getOperand(1);
    Value *newins = (fname == "llvm.umul.with.overflow.i64") ? builder.CreateMul(LHS, RHS)
         : builder.CreateAdd(LHS, RHS);
printf("[%s:%d] func %s\n", __FUNCTION__, __LINE__, fname.c_str());
    for(auto UI = II->user_begin(), UE = II->user_end(); UI != UE;) {
        auto UIN = std::next(UI);
        UI->replaceAllUsesWith(newins);
        recursiveDelete(*UI);
        UI = UIN;
    }
}

/*
 * Preprocess memcpy calls
 */
static void processMemcpy(CallInst *II)
{
    Instruction *dest = dyn_cast<Instruction>(II->getOperand(0));
    Argument *destArg = NULL;
    if (dest->getOpcode() == Instruction::BitCast)
        destArg = dyn_cast<Argument>(dest->getOperand(0));
    if (Instruction *source = dyn_cast<Instruction>(II->getOperand(1)))
    if (source->getOpcode() == Instruction::BitCast)
    if (dest->getOpcode() == Instruction::BitCast)
    if (Instruction *destTmp = dyn_cast<Instruction>(dest->getOperand(0))) {
    if (destTmp->getOpcode() == Instruction::Alloca) {
        if (Argument *sourceArg = dyn_cast<Argument>(source->getOperand(0))) {
            dest->getOperand(0);
            destTmp->replaceAllUsesWith(sourceArg);
            recursiveDelete(II);
            recursiveDelete(destTmp);
        }
        else if (Instruction *sourceTmp = dyn_cast<Instruction>(source->getOperand(0))) {
            if (sourceTmp->getOpcode() == Instruction::Alloca) {
//printf("[%s:%d] A->A\n", __FUNCTION__, __LINE__);
//destTmp->dump();
//sourceTmp->dump();
//Function *func = II->getParent()->getParent();
//func->dump();
                if (destTmp->getType() == sourceTmp->getType()) {
                destTmp->replaceAllUsesWith(sourceTmp);
                dest->setOperand(0, NULL);
                recursiveDelete(destTmp);
//destTmp->dump();
                recursiveDelete(II);
                }
                else {
printf("[%s:%d] memcpy/alloca, types not match %s\n", __FUNCTION__, __LINE__, II->getParent()->getParent()->getName().str().c_str());
II->dump();
destTmp->getType()->dump();
sourceTmp->getType()->dump();
                }
//printf("[%s:%d] aft\n", __FUNCTION__, __LINE__);
//func->dump();
            }
        }
    }
    }
}

/*
 * Perform any processing needed on the IR before execution.
 * This includes:
 *    * Removal of calls to dwarf debug functions
 *    * change all malloc/new calls to point to our runtime, so we can track them
 *    * Process/remove all 'methodToFunction' calls (which allow the generation
 *    *     of function pointers for class methods)
 * Context: Run after IR file load, before executing constructors.
 */
void preprocessModule(Module *Mod)
{
    // remove dwarf info, if it was compiled in
    static const char *delete_names[] = { "llvm.dbg.declare", "llvm.dbg.value", "atexit", NULL};
    const char **p = delete_names;
    while(*p)
        if (Function *Declare = Mod->getFunction(*p++)) {
            while (!Declare->use_empty()) {
                CallInst *CI = cast<CallInst>(Declare->user_back());
                CI->eraseFromParent();
            }
            Declare->eraseFromParent();
        }

    // remove Select statements; construct vtab tables
    for (auto FI = Mod->begin(), FE = Mod->end(); FI != FE; FI++)
        processSelect(&*FI);

    // process various function calls
    static struct {
        const char *name;
        void (*func)(CallInst *II);
    } callProcess[] = {
        // replace unsupported calls to llvm.umul.with.overflow.i64, llvm.uadd.with.overflow.i64
        {"llvm.umul.with.overflow.i64", processOverflow}, {"llvm.uadd.with.overflow.i64", processOverflow},
        // remap all calls to 'malloc' and 'new' to our runtime.
        {"_Znwm", processMalloc}, {"_Znam", processMalloc}, {"malloc", processMalloc},
        {"connectInterface", processConnectInterface},
        {"llvm.memcpy.p0i8.p0i8.i64", processMemcpy},
        {"_ZL20atomiccNewArrayCountm", processMSize},
        {"atomiccSchedulePriority", processPriority},
        {"atomiccInterfaceName", processInterfaceName},
        {NULL, NULL}};

    for (int i = 0; callProcess[i].name; i++) {
        if (Function *Declare = Mod->getFunction(callProcess[i].name))
        for(auto I = Declare->user_begin(), E = Declare->user_end(); I != E; ) {
            auto NI = std::next(I);
            callProcess[i].func(cast<CallInst>(*I));
            I = NI;
        }
    }
    TypeFinder StructTypes;
    StructTypes.run(*Mod, true);
    for (unsigned i = 0, e = StructTypes.size(); i != e; ++i) {
        StructType *STy = StructTypes[i];
        if (STy->isLiteral() || STy->getName().empty()) continue;
        getClass(STy);  // make sure that classCreate is initialized
        ClassMethodTable *table = classCreate[STy];
//printf("[%s:%d] STy %p table %p name %s map %s\n", __FUNCTION__, __LINE__, STy, table, getStructName(STy).c_str(), STy->structFieldMap.c_str());
        std::map<std::string, Function *> funcMap;
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
                std::string mname = ret.substr(idx+1);
                Function *func = Mod->getFunction(fname);
//printf("[%s:%d] %s mname %s fname %s func %p\n", __FUNCTION__, __LINE__, getStructName(STy).c_str(), mname.c_str(), fname.c_str(), func);
                if (func)  // do not put generic template protos into list
                    funcMap[mname] = func;
            }
            last_subs = subs;
        }
        for (auto item: funcMap) {
//printf("[%s:%d] sname %s first %s second %p name %s callingconv %x\n", __FUNCTION__, __LINE__, STy->getName().str().c_str(), item.first.c_str(), item.second, item.second->getName().str().c_str(), item.second->getCallingConv() == CallingConv::X86_VectorCall);
            if (item.second->getCallingConv() == CallingConv::X86_VectorCall)
            if (endswith(item.first, "__RDY") || endswith(item.first, "__READY")) {
                std::string enaName = item.first.substr(0, item.first.length() - 5);
                std::string enaSuffix = "__ENA";
                if (endswith(item.first, "__READY")) {
                    enaName = item.first.substr(0, item.first.length() - 7);
                    enaSuffix = "__VALID";
                }
                Function *enaFunc = funcMap[enaName];
                if (!enaFunc) {
                    printf("[%s:%d] %s function NULL\n", __FUNCTION__, __LINE__, enaName.c_str());
                    continue;
                }
                if (!isActionMethod(enaFunc))
                    enaSuffix = "";
                enaName += enaSuffix;
//printf("[%s:%d] sname %s func %s=%p %s=%p\n", __FUNCTION__, __LINE__, STy->getName().str().c_str(), item.first.c_str(), item.second, enaName.c_str(), enaFunc);
                table->method[enaName] = enaFunc;
                table->method[item.first] = item.second;
                ruleRDYFunction[enaFunc] = item.second; // must be before pushWork() calls
                ruleENAFunction[item.second] = enaFunc;
                // could be hoisted interface functions
                setSeen(enaFunc, enaName);
                setSeen(item.second, item.first);
            }
        }
    }
}
