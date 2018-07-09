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
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/OptimizationDiagnosticInfo.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"

using namespace llvm;

#include "AtomiccDecl.h"

static int trace_malloc;//= 1;
static int trace_fixup;//= 1;
int trace_pair;//= 1;

std::list<MEMORY_REGION> memoryRegion;

/* This unrolls loops
 */
static bool processLoops(Function *func)
{
    bool changed = false;
    DominatorTree *DT = new DominatorTree;
    PostDomTreeBase<BasicBlock> *PDT = new PostDomTreeBase<BasicBlock>();
    LoopInfo *LI = new LoopInfo;
    if (func->isDeclaration())
        return changed;
    DT->recalculate(*func);
    PDT->recalculate(*func);
    LI->analyze(*DT);
    SmallVector<Loop *, 4> PreOrderLoops = LI->getLoopsInReverseSiblingPreorder();
    printf("[%s:%d] START %s loopc %d\n", __FUNCTION__, __LINE__, func->getName().str().c_str(), (int)PreOrderLoops.size());
    if (PreOrderLoops.size()) {
        printf("[%s:%d]DT\n", __FUNCTION__, __LINE__);
        DT->print(errs());
        printf("[%s:%d]PDT\n", __FUNCTION__, __LINE__);
        PDT->print(errs());
        printf("[%s:%d]LI\n", __FUNCTION__, __LINE__);
        LI->print(errs());
        func->dump();
    }
    for (Loop *L : PreOrderLoops) {
printf("[%s:%d]LLLLLLLLLLLLLL %p\n", __FUNCTION__, __LINE__, L);
L->print(errs());
        if (!L->isLoopSimplifyForm()) { 
            printf("ERROROR:  Not unrolling loop which is not in loop-simplify form.\n");
            exit(-1);
        }
        unsigned TripCount = 16;
        unsigned TripMultiple = 1;
        unsigned Count = 16;
        bool Force = true;
        bool AllowRuntime = true;
        bool AllowExpensiveTripCount = true;
        bool PreserveCondBr = false;
        bool PreserveOnlyFirst = false;
        bool PreserveLCSSA = false;
        unsigned PeelCount = 0;

        TargetLibraryInfoImpl TLII(Triple(globalMod->getTargetTriple()));
        TargetLibraryInfo TLI(TLII);
        BlockFrequencyInfo BFI;
        AssumptionCache AC(*func);
        ScalarEvolution SE(*func, TLI, AC, *DT, *LI);
        OptimizationRemarkEmitter ORE(func, &BFI);
        changed |= llvm::UnrollLoop( L, Count, TripCount, Force, AllowRuntime,
            AllowExpensiveTripCount, PreserveCondBr, PreserveOnlyFirst,
            TripMultiple, PeelCount, LI, &SE, DT, &AC, &ORE, PreserveLCSSA);
printf("[%s:%d] before verifyDomTree %d\n", __FUNCTION__, __LINE__, changed);
        DT->verifyDomTree();
    }
    printf("[%s:%d]OVER\n", __FUNCTION__, __LINE__);
    if (changed)
        func->dump();
    return changed;
}


/*
 * Remove Alloca items inserted by clang as part of dwarf debug support.
 * (the 'this' pointer was copied into a stack temp rather than being
 * referenced directly from the parameter)
 * Context: Must be after processMethodToFunction
 */
static void processAlloca(Function *func)
{
    std::map<const Value *,Instruction *> remapValue;
    bool changed = processLoops(func); // must be before processAlloca
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
                IRBuilder<> builder(II->getParent());
                builder.SetInsertPoint(II);
                if (Function *cfunc = dyn_cast<Function>(ICL->getCalledValue())) {
                    if (cfunc->getName() == "llvm.memcpy.p0i8.p0i8.i64") {
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
                }
                break;
                }
            case Instruction::Add: {
                // these come from the loop expansion
                if (auto lhs = dyn_cast<ConstantInt>(II->getOperand(0)))
                if (auto rhs = dyn_cast<ConstantInt>(II->getOperand(1))) {
                    auto newItem = ConstantInt::get(II->getType(), lhs->getZExtValue() + rhs->getZExtValue());
                    II->replaceAllUsesWith(newItem);
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
    if (changed) {
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
func->dump();
    }
}

/*
 * Lookup vtable-referenced functions, changing IR to reference actual bound
 * function directly.  Also inline references to methods from the same class,
 * since these internal references must be inlined in generated verilog.
 */
static void processMethodInlining(Function *thisFunc, Function *parentFunc)
{
    processAlloca(thisFunc);
restart: // restart here after inlining function.... basic block structure might change
    for (auto BB = thisFunc->begin(), BE = thisFunc->end(); BB != BE; ++BB) {
        for (auto II = BB->begin(), IE = BB->end(); II != IE;) {
            auto PI = std::next(BasicBlock::iterator(II));
            if (CallInst *ICL = dyn_cast<CallInst>(II)) {
                Module *Mod = thisFunc->getParent();
                std::string callingName = thisFunc->getName();
                const StructType *callingSTy = findThisArgument(thisFunc);
                Value *callV = ICL->getCalledValue();
                const Function *func = getCallee(ICL);
                if (Instruction *oldOp = dyn_cast<Instruction>(callV)) {
                    std::string opName = printOperand(callV);
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
                    II->setOperand(II->getNumOperands()-1, const_cast<Function *>(func));
                    recursiveDelete(oldOp);
                }
                std::string calledName = func->getName();
                const StructType *STy = findThisArgument(func);
                //printf("%s: %s CALLS %s cSTy %p STy %p parentFunc %p func %p thisFunc %p\n", __FUNCTION__, callingName.c_str(), calledName.c_str(), callingSTy, STy, parentFunc, func, thisFunc);
                if (parentFunc != func && thisFunc != func)
                if (callingSTy == STy) {
                    //fprintf(stdout,"callProcess: %s cName %s single!!!!\n", callingName.c_str(), calledName.c_str());
                    processMethodInlining(const_cast<Function *>(func), parentFunc);
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

/*
 * Add a function to the processing list for generation of cpp and verilog.
 */
void pushWork(Function *func, std::string mName)
{
    //printf("[%s:%d] mname %s funcname %s\n", __FUNCTION__, __LINE__, mName.c_str(), func->getName().str().c_str());
    getClass(findThisArgument(func))->method[mName] = func;
    // inline intra-class method call bodies
    processMethodInlining(func, func);
}

/*
 * Process 'blocks' functions that were generated for user rules.
 * The blocks context is removed; the functions are transformed into
 * a method (and its associated RDY method), attached to the containing class.
 */
extern "C" Function *fixupFunction(uint64_t *bcap, Function *argFunc)
{
    ValueToValueMapTy VMap;
    SmallVector<ReturnInst*, 8> Returnsfunc;  // Ignore returns cloned.

    // first clone template function into temp function, so that we can
    // edit, filling in actual captured data values
    if (trace_fixup) {
        printf("[%s:%d] BEFORECLONE func %p\n", __FUNCTION__, __LINE__, argFunc);
        argFunc->dump();
    }
    Type *Params[] = {argFunc->arg_begin()->getType()};
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
            //printf("[%s:%d] Load %lld\n", __FUNCTION__, __LINE__, val);
            VMap[arg] = ConstantInt::get(arg->getType(), val);
        }
    }
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
argFunc->dump();
func->dump();
    CloneFunctionInto(func, argFunc, VMap, false, Returnsfunc, "", nullptr);
    processAlloca(func);
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
extern "C" void addBaseRule(const char *name, uint64_t *bcap, Function *ardyFunc, Function *aenaFunc)
{
    ClassMethodTable *table = getClass(findThisArgument(aenaFunc));
    std::string tempName = name;
    for (unsigned i = 0; i < aenaFunc->arg_size() - 1; i++)
        tempName += "_" + utostr(bcap[i]);
    std::string enaName = tempName;
    int counter = 100;
    // if necessary to avoid conflicts, generate unique rule names
    while (table->method[enaName + "__ENA"])
        enaName = tempName + "$" + utostr(counter++);
    Function *enaFunc = fixupFunction(bcap, aenaFunc);
    if (trace_pair)
        printf("[%s:%d] name %s size %ld ena %s\n", __FUNCTION__, __LINE__, enaName.c_str(), aenaFunc->arg_size(), enaFunc->getName().str().c_str());
    table->ruleFunctions[enaName + "__ENA"] = true;
    pushWork(enaFunc, enaName + "__ENA");
    if (ardyFunc) {
        table->ruleFunctions[enaName + "__RDY"] = true;
        pushWork(fixupFunction(bcap, ardyFunc), enaName + "__RDY");
    }
}

/*
 * Called from user constructors to set priority on a rule
 */
extern "C" void atomiccSchedulePriority(const char *rule, const char *priority, const StructType *STy)
{
    ClassMethodTable *table = getClass(STy);
    printf("%s: %s %s %p\n", __FUNCTION__, rule, priority, STy);
    STy->dump();
    table->IR->priority[rule] = priority;
}
