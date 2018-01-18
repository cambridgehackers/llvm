//===-- AtomiccMap.cpp - Generating Verilog from LLVM -----===//
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

static int trace_map;//= 1;
static int trace_dump_malloc;//= 1;

typedef struct {
    const void *addr;
    const void *type;
} MAPSEEN_TYPE;
struct MAPSEENcomp {
    bool operator() (const MAPSEEN_TYPE& lhs, const MAPSEEN_TYPE& rhs) const {
        if (lhs.addr < rhs.addr)
            return true;
        if (lhs.addr > rhs.addr)
            return false;
        return lhs.type < rhs.type;
    }
};
typedef std::map<std::string, Function *>MethodMapType;

static std::map<MAPSEEN_TYPE, int, MAPSEENcomp> addressTypeAlreadyProcessed;

/*
 * Dump all statically allocated and malloc'ed data areas
 */
void dumpMemoryRegions(int arg)
{
    printf("%s: %d\n", __FUNCTION__, arg);
    for (MEMORY_REGION info : memoryRegion) {
        const GlobalValue *g = EE->getGlobalValueAtAddress(info.p);
        std::string gname;
        if (g)
            gname = g->getName();
        printf("Region addr %p name '%s'", info.p, gname.c_str());
        if (info.STy)
            printf(" infoSTy %s", info.STy->getName().str().c_str());
        printf("\n");
        if (info.type)
            info.type->dump();
        long size = info.size;
        if (size > GIANT_SIZE) {
           size -= GIANT_SIZE;
           size -= 10 * sizeof(int);
           size = size/2;
        }
        size += 16;
        memdumpl((unsigned char *)info.p, size, "data");
    }
}

/*
 * Verify that an address lies within a valid user data area.
 */
static int validateAddress(int arg, void *p)
{
    static int once;
    for (MEMORY_REGION info : memoryRegion) {
        if (p >= info.p && (size_t)p < ((size_t)info.p + info.size))
            return 0;
    }
    printf("%s: %d address validation failed %p\n", __FUNCTION__, arg, p);
    if (!once)
    for (MEMORY_REGION info : memoryRegion) {
        const GlobalValue *g = EE->getGlobalValueAtAddress(info.p);
        const char *cp = "";
        if (g)
            cp = g->getName().str().c_str();
        printf("%p %s size 0x%lx\n", info.p, cp, info.size);
    }
    once = 1;
    return 1;
}

/*
 * Local version of 'ReplaceAllUsesWith'(RAUW) that allows changing the
 * datatype as part of the replcement.
 */
static void myReplaceAllUsesWith(Value *Old, Value *New)
{
  //assert(New->getType() == Old->getType() && "replaceAllUses of value with new value of different type!");
  // Notify all ValueHandles (if present) that Old value is going away.
  //if (Old->HasValueHandle)
    //ValueHandleBase::ValueIsRAUWd(Old, New);
  if (Old->isUsedByMetadata())
    ValueAsMetadata::handleRAUW(Old, New);
  while (!Old->use_empty()) {
    Use &U = *Old->use_begin();
    // Must handle Constants specially, we cannot call replaceUsesOfWith on a
    // constant because they are uniqued.
    if (auto *C = dyn_cast<Constant>(U.getUser())) {
      if (!isa<GlobalValue>(C)) {
        C->handleOperandChange(Old, New); //, &U);
        continue;
      }
    }
    U.set(New);
  }
  if (BasicBlock *BB = dyn_cast<BasicBlock>(Old))
    BB->replaceSuccessorsPhiUsesWith(cast<BasicBlock>(New));
}

/*
 * For pointers in a class that were allocated by methods in the class,
 * allocate them statically as part of the class object itself.
 */
static void inlineReferences(Module *Mod, const StructType *STy, uint64_t Idx, Type *newType)
{
    for (auto FB = Mod->begin(), FE = Mod->end(); FB != FE; ++FB) {
        if (FB->getName().substr(0, 21) != "unused_block_function")
        for (auto BB = FB->begin(), BE = FB->end(); BB != BE; ++BB)
            for (auto II = BB->begin(), IE = BB->end(); II != IE; ) {
                BasicBlock::iterator PI = std::next(BasicBlock::iterator(II));
                if (LoadInst *IL = dyn_cast<LoadInst>(&*II)) {
                if (GetElementPtrInst *IG = dyn_cast<GetElementPtrInst>(IL->getOperand(0))) {
                    gep_type_iterator I = gep_type_begin(IG), E = gep_type_end(IG);
                    Constant *FirstOp = dyn_cast<Constant>(I.getOperand());
                    if (I++ != E && FirstOp && FirstOp->isNullValue()
                     && I != E && STy == dyn_cast<StructType>(I.getIndexedType()))
                        if (const ConstantInt *CI = dyn_cast<ConstantInt>(I.getOperand()))
                            if (CI->getZExtValue() == Idx) {
                                 IG->mutateType(newType);
                                 myReplaceAllUsesWith(IL, IG);
                                 IL->eraseFromParent();
                            }
                    }
                }
                II = PI;
            }
    }
}

/*
 * Check if one StructType inherits another one.
 */
static int derivedStruct(const StructType *STyA, const StructType *STyB)
{
    int Idx = 0;
    if (STyA && STyB) {
        if (STyA == STyB)
            return 1;     // all types are derived from themselves
        //BUG: this only checks 1 level of derived???
        for (auto I = STyA->element_begin(), E = STyA->element_end(); I != E; ++I, Idx++)
            if (fieldName(STyA, Idx) == "" && dyn_cast<StructType>(*I) && *I == STyB)
                return 1;
    }
    return 0;
}

static int checkDerived(const Type *A, const Type *B)
{
    if (const PointerType *PTyA = cast_or_null<PointerType>(A))
    if (const PointerType *PTyB = cast_or_null<PointerType>(B))
        return derivedStruct(dyn_cast<StructType>(PTyA->getElementType()),
                             dyn_cast<StructType>(PTyB->getElementType()));
    return 0;
}

static void mapType(Module *Mod, char *addr, Type *Ty, std::string aname)
{
    const DataLayout TD = EE->getDataLayout();
    if (!addr || addr == BOGUS_POINTER
     || addressTypeAlreadyProcessed[MAPSEEN_TYPE{addr, Ty}])
        return;
    addressTypeAlreadyProcessed[MAPSEEN_TYPE{addr, Ty}] = 1;
    if (trace_map)
        printf("%s: addr %p TID %d Ty %p name %s\n", __FUNCTION__, addr, Ty->getTypeID(), Ty, aname.c_str());
    if (validateAddress(3010, addr))
        printf("%s: bad addr %p TID %d Ty %p name %s\n", __FUNCTION__, addr, Ty->getTypeID(), Ty, aname.c_str());
    switch (Ty->getTypeID()) {
    case Type::StructTyID: {
        StructType *STy = cast<StructType>(Ty);
        const StructLayout *SLO = TD.getStructLayout(STy);
        getClass(STy); // allocate classCreate
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            std::string fname = fieldName(STy, Idx);
            char *eaddr = addr + SLO->getElementOffset(Idx);
            Type *element = *I;
            if (PointerType *PTy = dyn_cast<PointerType>(element)) {
                void *p = *(char **)eaddr;
                int setInterface = fname != "";
                /* Look up destination address in allocated regions, to see
                 * what if its datatype is a derived type from the pointer
                 * target type.  If so, replace pointer base type.
                 */
                if (trace_map)
                    printf("%s: Pointer lookup %p STy %s fname %s\n", __FUNCTION__, p, STy->hasName() ? STy->getName().str().c_str() : "none", fname.c_str());
                static int once;
                for (MEMORY_REGION info : memoryRegion) {
                    if (trace_map && !once)
                        printf("%s: info.p %p info.p+info.size %lx\n", __FUNCTION__, info.p, ((size_t)info.p + info.size));
                    if (p >= info.p && (size_t)p < ((size_t)info.p + info.size)) {
                    if (checkDerived(info.type, PTy)) {
                        getClass(STy)->replaceType[Idx] = info.type;
                        getClass(STy)->IR->replaceCount[Idx] = info.vecCount;
                        //if (trace_map)
                            printf("%s: pointerFound %p info.STy %s count %d\n", __FUNCTION__, p, info.STy->getName().str().c_str(), (int)info.vecCount);
                        if (STy == info.STy) {
                            getClass(STy)->IR->allocateLocally[Idx] = true;
                            inlineReferences(Mod, STy, Idx, info.type);
                            getClass(STy)->replaceType[Idx] = cast<PointerType>(info.type)->getElementType();
                            setInterface = 0;
                        }
                    }
                    else {
                        if (trace_map)
                            printf("%s: notderived %p info.STy %p %s\n", __FUNCTION__, p, info.STy, info.STy?info.STy->getName().str().c_str():"null");
                    }
                    }
                }
                once = 1;
            }
            if (fname != "") {
                if (trace_map)
                    printf("%s: recurse mapType for %s\n", __FUNCTION__, (aname + "$$" + fname).c_str());
                mapType(Mod, eaddr, element, aname + "$$" + fname);
            }
            else if (dyn_cast<StructType>(element))
                mapType(Mod, eaddr, element, aname);
        }
        break;
        }
    case Type::PointerTyID: {
        Type *element = cast<PointerType>(Ty)->getElementType();
        if (element->getTypeID() != Type::FunctionTyID)
            mapType(Mod, *(char **)addr, element, aname);
        break;
    }
    default:
        break;
    }
}

/*
 * Starting from all toplevel global variables, construct symbolic names for
 * all reachable addresses
 */
void constructAddressMap(Module *Mod)
{
printf("[%s:%d] start\n", __FUNCTION__, __LINE__);
    for (auto MI = Mod->global_begin(), ME = Mod->global_end(); MI != ME; MI++) {
        void *addr = EE->getPointerToGlobal(&*MI);
        Type *Ty = MI->getType()->getElementType();
        memoryRegion.push_back(MEMORY_REGION{addr,
            EE->getDataLayout().getTypeAllocSize(Ty), MI->getType(), NULL, 0});
        mapType(Mod, (char *)addr, Ty, MI->getName());
    }
    if (trace_dump_malloc)
        dumpMemoryRegions(4010);
}
