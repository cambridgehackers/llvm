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

/*
 * Map calls to 'new()' and 'malloc()' in constructors to call 'llvm_translate_malloc'.
 * This enables llvm-translate to easily maintain a list of valid memory regions
 * during processing.
 */
Value *findElementCount(Instruction *I)
{
    Value *ret = NULL;
    if (I) {
        if (I->getOpcode() == Instruction::Select)
            I = cast<Instruction>(I->getOperand(2));
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
        bool replaceMul = false;
        if (auto ins = dyn_cast<ExtractValueInst>(*UI))
        if (ins->getNumIndices() == 1 && ins->getIndices()[0] == 0)
            replaceMul = true;
        UI->replaceAllUsesWith(replaceMul ? newins : ConstantInt::get(UI->getType(), 0));
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

    // process various function calls
    static struct {
        const char *name;
        void (*func)(CallInst *II);
    } callProcess[] = {
        // replace unsupported calls to llvm.umul.with.overflow.i64, llvm.uadd.with.overflow.i64
        {"llvm.umul.with.overflow.i64", processOverflow}, {"llvm.uadd.with.overflow.i64", processOverflow},
        // remap all calls to 'malloc' and 'new' to our runtime.
        {"_Znwm", processMalloc}, {"_Znam", processMalloc}, {"malloc", processMalloc},
        {"llvm.memcpy.p0i8.p0i8.i64", processMemcpy},
        {"_ZL20atomiccNewArrayCountm", processMSize},
        {"atomiccSchedulePriority", processPriority},
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
        if (!STy->isLiteral() && !STy->getName().empty())
            getClass(STy); // make sure that classCreate is initialized
    }
}
