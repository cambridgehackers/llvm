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

using namespace llvm;

#include "AtomiccDecl.h"

static llvm::cl::opt<bool>
    workTrace("worktrace", llvm::cl::Optional, llvm::cl::desc("trace clang method processing"));
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
bool trace = false; //func->getName() == "_ZN12AdapterToBusI7NOCDatajE6in$enqES0_i";
if (trace) {
printf("[%s:%d]BEFORE\n", __FUNCTION__, __LINE__);
func->dump();
}
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
                if (target->getOpcode() == Instruction::Alloca && endswith(target->getName(), ".addr")) {
                    if (!dyn_cast<CallInst>(II->getOperand(0))) { // don't do remapping for calls
                    // remember values stored in Alloca temps
                    remapValue[target] = II;
if (trace) {
printf("[%s:%d] STORE target %p II %p\n", __FUNCTION__, __LINE__, (void *)target, (void *)II);
target->dump();
II->dump();
}
                    }
                }
                }
                break;
            case Instruction::Load:
                if (Instruction *val = remapValue[II->getOperand(0)]) {
                    // replace loads from temp areas with stored values
if (trace) {
printf("[%s:%d] LOAD %p\n", __FUNCTION__, __LINE__, (void *)val);
II->dump();
}
                    II->replaceAllUsesWith(val->getOperand(0));
                    recursiveDelete(II);
                }
                break;
            case Instruction::Call: {
                CallInst *ICL = dyn_cast<CallInst>(II);
                Value *called = II->getOperand(II->getNumOperands()-1);
                Function *CF = dyn_cast<Function>(called);
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
                        if (trace) {
                            printf("[%s:%d] deleting call\n", __FUNCTION__, __LINE__);
                            II->dump();
                        }
                        recursiveDelete(II);
                        goto restart;
                    }
                    }
                }
                if (II->getNumOperands() >= 2)
                for (unsigned int i = 0; i < II->getNumOperands() - 2; i++) {
                    if (Instruction *val = remapValue[II->getOperand(i)]) {
if (trace) {
printf("[%s:%d] remapcall %d\n", __FUNCTION__, __LINE__, i);
II->dump();
}
                        SmallVector<llvm::Value *, 4> Args;
                        Args.resize(II->getNumOperands()-1);
                        for (unsigned int j = 0; j < II->getNumOperands() - 1; j++)
                            if (j == i)
                                Args[j] = val->getOperand(0);
                            else
                                Args[j] = II->getOperand(j);
                        auto nitem = builder.CreateCall(CF, Args);
if (trace) {
printf("[%s:%d]\n", __FUNCTION__, __LINE__);
nitem->dump();
}
                        II->replaceAllUsesWith(nitem);
                        II->eraseFromParent();
                        goto restart;
                    }
                }
                break;
                }
            case Instruction::Add:
                // these come from the loop expansion
#if 0 // need to preserve component values so that generic processing is correct
                if (auto lhs = dyn_cast<ConstantInt>(II->getOperand(0)))
                if (auto rhs = dyn_cast<ConstantInt>(II->getOperand(1))) {
                    auto newItem = ConstantInt::get(II->getType(), lhs->getZExtValue() + rhs->getZExtValue());
                    II->replaceAllUsesWith(newItem);
                    recursiveDelete(II);
                    goto restart;
                }
#endif
                break;
            };
            IIb = PI;
        }
    }
    for (auto item: remapValue) {
        if (item.second)
        if (Instruction *allocItem = dyn_cast<Instruction>(item.second->getOperand(1))) {
if (trace) {
printf("[%s:%d]remap\n", __FUNCTION__, __LINE__);
allocItem->dump();
}
            int count = 0;
            for (auto UB = allocItem->use_begin(), UE = allocItem->use_end(); UB != UE; UB++) {
                if (auto II = dyn_cast<Instruction>(UB->getUser()))
                if (II->getOpcode() == Instruction::Store)
                    continue;
                count++;
            }
            if (count < 2)
            for (auto UB = allocItem->use_begin(), UE = allocItem->use_end(); UB != UE; UB++)
                if (auto II = dyn_cast<Instruction>(UB->getUser()))
                if (II->getOpcode() == Instruction::Store)
                    II->eraseFromParent();
        }
    }
if (trace) {
printf("[%s:%d]AFTER\n", __FUNCTION__, __LINE__);
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
void pushWork(ClassMethodTable *table, Function *func, std::string mName)
{
    if (workTrace) {
        printf("[%s:%d] mname %s funcname %s\n", __FUNCTION__, __LINE__, mName.c_str(), func->getName().str().c_str());
        func->dump();
    }
    table->methods.push_back(ClassMethodInfo{mName, func});
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
        printf("[%s:%d] BEFORECLONE func %p\n", __FUNCTION__, __LINE__, (void *)argFunc);
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
//printf("[%s:%d]\n", __FUNCTION__, __LINE__);
//argFunc->dump();
//func->dump();
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
extern "C" void *llvm_translate_malloc(size_t size, Type *type, const StructType *STy, int64_t vecCount)
{
    size_t newsize = size * 2 + MAX_BASIC_BLOCK_FLAGS * sizeof(int) + GIANT_SIZE;
    void *ptr = malloc(newsize);
    std::string vecCountStr;
    if (vecCount != -1)
        vecCountStr = utostr(vecCount);
    memset(ptr, 0x5a, newsize);
    if (trace_malloc)
        printf("[%s:%d] %ld = %p type %p sty %p vecCount %ld\n", __FUNCTION__, __LINE__, size, (void *)ptr, (void *)type, (void *)STy, (long)vecCount);
    memoryRegion.push_back(MEMORY_REGION{ptr, newsize, type, STy, vecCountStr});
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
    while(1) {
next:
        for(auto item: table->methods)
            if (item.name == enaName + "__ENA") {
                enaName = tempName + DOLLAR + utostr(counter++);
                goto next;
            }
        break;
    }
    Function *enaFunc = fixupFunction(bcap, aenaFunc);
    if (trace_pair)
        printf("[%s:%d] name %s size %ld ena %s\n", __FUNCTION__, __LINE__, enaName.c_str(), aenaFunc->arg_size(), enaFunc->getName().str().c_str());
    table->ruleFunctions[enaName + "__ENA"] = true;
    pushWork(table, enaFunc, enaName + "__ENA");
    if (ardyFunc) {
        table->ruleFunctions[enaName + "__RDY"] = true;
        pushWork(table, fixupFunction(bcap, ardyFunc), enaName + "__RDY");
    }
}

/*
 * Called from user constructors to set priority on a rule
 */
extern "C" void atomiccSchedulePriority(const char *rule, const char *priority, const StructType *STy)
{
    ClassMethodTable *table = getClass(STy);
    printf("%s: %s %s %p\n", __FUNCTION__, rule, priority, (void *)STy);
    STy->dump();
    table->priority[rule] = priority;
}
