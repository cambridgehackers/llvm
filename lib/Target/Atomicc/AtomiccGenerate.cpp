//===-- AtomiccGenerate.cpp - Generating Verilog from LLVM -----===//
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
#include <stdio.h>
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

#include "AtomiccDecl.h"

#define MODULE_ARROW MODULE_SEPARATOR
#define MODULE_DOT   MODULE_SEPARATOR

static int trace_function;//=1;
static int trace_call;//=1;
static int trace_gep;//=1;
static int trace_operand;//=1;
static int trace_hoist;//= 1;
static std::map<const StructType *,ClassMethodTable *> classCreate;
static unsigned NextTypeID;

static std::map<const Value *, std::string> allocaMap;
static DenseMap<const Value*, unsigned> AnonValueNumbers;
static unsigned NextAnonValueNumber;
static DenseMap<const StructType*, unsigned> UnnamedStructIDs;
Module *globalMod;
std::map<const Function *,std::list<StoreListElement>> storeList;
std::map<const Function *,std::list<const Instruction *>> functionList;
std::map<const Function *,std::list<CallListElement>> callList;
static std::string globalMethodName;

static INTMAP_TYPE predText[] = {
    {FCmpInst::FCMP_FALSE, "false"}, {FCmpInst::FCMP_OEQ, "oeq"},
    {FCmpInst::FCMP_OGT, "ogt"}, {FCmpInst::FCMP_OGE, "oge"},
    {FCmpInst::FCMP_OLT, "olt"}, {FCmpInst::FCMP_OLE, "ole"},
    {FCmpInst::FCMP_ONE, "one"}, {FCmpInst::FCMP_ORD, "ord"},
    {FCmpInst::FCMP_UNO, "uno"}, {FCmpInst::FCMP_UEQ, "ueq"},
    {FCmpInst::FCMP_UGT, "ugt"}, {FCmpInst::FCMP_UGE, "uge"},
    {FCmpInst::FCMP_ULT, "ult"}, {FCmpInst::FCMP_ULE, "ule"},
    {FCmpInst::FCMP_UNE, "une"}, {FCmpInst::FCMP_TRUE, "true"},
    {ICmpInst::ICMP_EQ, "=="}, {ICmpInst::ICMP_NE, "!="},
    {ICmpInst::ICMP_SGT, ">"}, {ICmpInst::ICMP_SGE, ">="},
    {ICmpInst::ICMP_SLT, "<"}, {ICmpInst::ICMP_SLE, "<="},
    {ICmpInst::ICMP_UGT, ">"}, {ICmpInst::ICMP_UGE, ">="},
    {ICmpInst::ICMP_ULT, "<"}, {ICmpInst::ICMP_ULE, "<="}, {}};
static INTMAP_TYPE opcodeMap[] = {
    {Instruction::Add, "+"}, {Instruction::FAdd, "+"},
    {Instruction::Sub, "-"}, {Instruction::FSub, "-"},
    {Instruction::Mul, "*"}, {Instruction::FMul, "*"},
    {Instruction::UDiv, "/"}, {Instruction::SDiv, "/"}, {Instruction::FDiv, "/"},
    {Instruction::URem, "%"}, {Instruction::SRem, "%"}, {Instruction::FRem, "%"},
    {Instruction::And, "&"}, {Instruction::Or, "|"}, {Instruction::Xor, "^"},
    {Instruction::Shl, "<<"}, {Instruction::LShr, ">>"}, {Instruction::AShr, " >> "}, {}};
std::map<const Function *, Function *> ruleRDYFunction;
std::map<const Function *, const Function *> ruleENAFunction;
static struct {
    std::map<const BasicBlock *, Value *> val;
} blockCondition[2];

/*
 * Utility functions
 */
extern "C" void parseError(void)
{
}
const char *intmapLookup(INTMAP_TYPE *map, int value)
{
    while (map->name) {
        if (map->value == value)
            return map->name;
        map++;
    }
    return "unknown";
}

static const AllocaInst *isDirectAlloca(const Value *V)
{
    const AllocaInst *AA = dyn_cast<AllocaInst>(V);
    if (!AA || AA->isArrayAllocation()
     || AA->getParent() != &AA->getParent()->getParent()->getEntryBlock())
        return 0;
    return AA;
}
static bool isAlloca(const Value *arg)
{
    if (const GetElementPtrInst *IG = dyn_cast_or_null<GetElementPtrInst>(arg))
        arg = dyn_cast<Instruction>(IG->getPointerOperand());
    if (const Instruction *source = dyn_cast_or_null<Instruction>(arg))
    if (source->getOpcode() == Instruction::Alloca)
            return true;
    return false;
}
static bool isAddressExposed(const Value *V)
{
    return isa<GlobalVariable>(V) || isDirectAlloca(V);
}
/*
 * Return the name of the 'ind'th field of a StructType.
 * This code depends on a modification to llvm/clang that generates structFieldMap.
 */
std::string fieldName(const StructType *STy, uint64_t ind)
{
    return getClass(STy)->fieldName[ind];
}

bool isInterface(const StructType *STy)
{
    return STy && getStructName(STy).substr(0, 12) == "l_ainterface";
}

bool isActionMethod(const Function *func)
{
    return (func->getReturnType() == Type::getVoidTy(func->getContext()));
}

static void checkClass(const StructType *STy, const StructType *ActSTy)
{
    ClassMethodTable *table = getClass(STy);
    //ClassMethodTable *atable = getClass(ActSTy);
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        const Type *element = *I;
        if (table)
            if (const Type *newType = table->replaceType[Idx])
                element = newType;
        std::string fname = fieldName(STy, Idx);
        if (const StructType *iSTy = dyn_cast<StructType>(element)) {
            if (fname == "")
                checkClass(iSTy, ActSTy);
        }
    }
}

ClassMethodTable *getClass(const StructType *STy)
{
    int fieldSub = 0;
    if (!classCreate[STy]) {
        ClassMethodTable *table = new ClassMethodTable;
        classCreate[STy] = table;
        classCreate[STy]->STy = STy;
        int len = STy->structFieldMap.length();
        int subs = 0, last_subs = 0;
        int processSequence = 0; // seq=0 -> fields
        while (subs < len) {
            while (subs < len && STy->structFieldMap[subs] != ',') {
                subs++;
            }
            subs++;
            if (STy->structFieldMap[last_subs] == '/') {
                processSequence++; // seq=1 -> methods
                last_subs++;
            }
            if (STy->structFieldMap[last_subs] == ';') {
                processSequence++; // seq=2 -> software interfaces
                last_subs++;
            }
            if (STy->structFieldMap[last_subs] == '@') {
                processSequence++; // seq=3 -> interface connect
                last_subs++;
            }
            std::string ret = STy->structFieldMap.substr(last_subs);
            int idx = ret.find(',');
            if (idx >= 0)
                ret = ret.substr(0,idx);
            idx = ret.find(':');
//printf("[%s:%d] sequence %d ret %s idx %d\n", __FUNCTION__, __LINE__, processSequence, ret.c_str(), idx);
            if (processSequence == 0)
                table->fieldName[fieldSub++] = ret;
            else if (processSequence == 2)
                table->softwareName[ret] = 1;
            else if (processSequence == 3) {
                int ind = ret.find(":");
                std::string source = ret.substr(ind+1);
                std::string target = ret.substr(0, ind);
                std::string targetItem = target, targetInterface;
                ind = targetItem.find("$");
                if (ind > 0) {
                    targetInterface = targetItem.substr(ind+1);
                    targetItem = targetItem.substr(0, ind);
                }
                int Idx = 0;
                for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
                    if (const StructType *STyE = dyn_cast<StructType>(*I))
                    if (targetItem == fieldName(STy, Idx)) {
                        int Idx = 0;
                        for (auto I = STyE->element_begin(), E = STyE->element_end(); I != E; ++I, Idx++) {
                            if (const PointerType *PTy = dyn_cast<PointerType>(*I))
                            if (const StructType *STyI = dyn_cast<StructType>(PTy->getElementType()))
                            if (targetInterface == fieldName(STyE, Idx)) {
printf("[%s:%d] FOUND sname %s\n", __FUNCTION__, __LINE__, STyI->getName().str().c_str());
                                table->interfaceConnect.push_back(InterfaceConnectType{target, source, STyI});
                                goto nextInterface;
                            }
                        }
                    }
                }
        nextInterface:;
            }
            else if (idx >= 0) {
                std::string fname = ret.substr(0, idx);
                Function *func = globalMod->getFunction(fname);
                std::string mName = ret.substr(idx+1);
                if (func)
                    table->funcMap[mName] = {fname, func};
//printf("[%s:%d] fname %s mName %s func %p\n", __FUNCTION__, __LINE__, fname.c_str(), mName.c_str(), func);
                }
            last_subs = subs;
        }
        checkClass(STy, STy);
    }
    return classCreate[STy];
}

/*
 * Name functions
 */
std::string getStructName(const StructType *STy)
{
    assert(STy);
    getClass(STy);
    if (!STy->isLiteral() && !STy->getName().empty()) {
        std::string temp = STy->getName().str();
        if (temp.substr(0,7) == "emodule")
            temp = temp.substr(1);
        return CBEMangle("l_" + temp);
    }
    if (!UnnamedStructIDs[STy])
        UnnamedStructIDs[STy] = NextTypeID++;
    return "l_unnamed_" + utostr(UnnamedStructIDs[STy]);
}

std::string GetValueName(const Value *Operand)
{
    const GlobalAlias *GA = dyn_cast<GlobalAlias>(Operand);
    const Value *V;
    if (GA && (V = GA->getAliasee()))
        Operand = V;
    if (const GlobalValue *GV = dyn_cast<GlobalValue>(Operand))
        return CBEMangle(GV->getName());
    std::string Name = Operand->getName();
    if (Name.empty()) { // Assign unique names to local temporaries.
        unsigned &No = AnonValueNumbers[Operand];
        if (No == 0)
            No = ++NextAnonValueNumber;
        Name = "tmp__" + utostr(No);
    }
    std::string VarName = allocaMap[Operand];
    if (VarName == "")
    for (auto charp = Name.begin(), E = Name.end(); charp != E; ++charp) {
        char ch = *charp;
        if (isalnum(ch) || ch == '_' || ch == '$')
            VarName += ch;
        else {
            char buffer[5];
            sprintf(buffer, "_%x_", ch);
            VarName += buffer;
        }
    }
    return VarName;
}

static const StructType *findThisArgumentType(const PointerType *PTy, int ind)
{
    if (PTy)
    if (const FunctionType *func = dyn_cast<FunctionType>(PTy->getElementType()))
    if (func->getNumParams() > 0)
    if ((PTy = dyn_cast<PointerType>(func->getParamType(ind))))
    if (const StructType *STy = dyn_cast<StructType>(PTy->getElementType())) {
        getClass(STy);
        return STy;
    }
    return NULL;
}
const StructType *findThisArgument(const Function *func)
{
    return findThisArgumentType(func->getType(), false);
}

/*
 * Output type declarations.  Note that each case in the switch statement
 * is different for verilog and cpp.
 */
std::string printType(const Type *Ty, bool isSigned, std::string NameSoFar, std::string prefix, std::string postfix, bool ptr)
{
    std::string sep, cbuffer = prefix, sp = (isSigned?"signed":"unsigned");
    int thisId = Ty->getTypeID();
    switch (thisId) {
    case Type::VoidTyID:
        cbuffer += "VERILOG_void " + NameSoFar;
        break;
    case Type::IntegerTyID: {
        unsigned NumBits = cast<IntegerType>(Ty)->getBitWidth();
if (NumBits != 1 && NumBits != 8 && NumBits != 32 && NumBits != 64) {
printf("[%s:%d] NUMBITS %d\n", __FUNCTION__, __LINE__, NumBits);
}
        assert(NumBits <= 128 && "Bit widths > 128 not implemented yet");
        if (NumBits == 1)
            cbuffer += "VERILOG_bool";
        else if (NumBits <= 8) {
            if (ptr)
                cbuffer += sp + " VERILOG_char";
            else
                cbuffer += "reg";
        }
        else if (NumBits <= 16)
            cbuffer += sp + " VERILOG_short";
        else if (NumBits <= 32)
            //cbuffer += sp + " VERILOG_int";
            cbuffer += "reg" + verilogArrRange(Ty);
        else if (NumBits <= 64)
            cbuffer += sp + " VERILOG_long long";
        cbuffer += " " + NameSoFar;
        break;
        }
    case Type::FunctionTyID: {
        const FunctionType *FTy = cast<FunctionType>(Ty);
        const Type *retType = FTy->getReturnType();
        auto AI = FTy->param_begin(), AE = FTy->param_end();
        bool structRet = AI != AE && (*AI) != Type::getInt8PtrTy(globalMod->getContext());
        if (structRet) {  //FTy->hasStructRetAttr()
//printf("[%s:%d] structret\n", __FUNCTION__, __LINE__);
//exit(-1);
            if (auto PTy = dyn_cast<PointerType>(*AI))
                retType = PTy->getElementType();
            AI++;
        }

        std::string tstr = " (" + NameSoFar + ") (";
        for (;AI != AE; ++AI) {
            Type *element = *AI;
            if (sep != "")
            if (auto PTy = dyn_cast<PointerType>(element))
                element = PTy->getElementType();
            tstr += printType(element, /*isSigned=*/false, "", sep, "", false);
            sep = ", ";
        }
        if (FTy->isVarArg()) {
            if (!FTy->getNumParams())
                tstr += " VERILOG_int"; //dummy argument for empty vaarg functs
            tstr += ", ...";
        } else if (!FTy->getNumParams())
            tstr += "VERILOG_void";
        cbuffer += printType(retType, /*isSigned=*/false, tstr + ')', "", "", false);
        break;
        }
    case Type::StructTyID: {
        const StructType *STy = cast<StructType>(Ty);
        cbuffer += getStructName(STy) + " " + NameSoFar;
        break;
        }
    case Type::ArrayTyID: {
        const ArrayType *ATy = cast<ArrayType>(Ty);
        unsigned len = ATy->getNumElements();
        if (len == 0) len = 1;
        cbuffer += printType(ATy->getElementType(), false, "", "", "", false) + NameSoFar + "[" + utostr(len) + "]";
        break;
        }
    case Type::PointerTyID: {
        const PointerType *PTy = cast<PointerType>(Ty);
        std::string ptrName = "*" + NameSoFar;
        if (PTy->getElementType()->isArrayTy() || PTy->getElementType()->isVectorTy())
            ptrName = "(" + ptrName + ")";
        cbuffer += printType(PTy->getElementType(), false, ptrName, "", "", true);
        break;
        }
    default:
        llvm_unreachable("Unhandled case in printType!");
    }
    cbuffer += postfix;
    return cbuffer;
}

/*
 * Calculate offset from base pointer for GEP
 */
int64_t getGEPOffset(VectorType **LastIndexIsVector, gep_type_iterator I, gep_type_iterator E)
{
    uint64_t Total = 0;
    const DataLayout TD = EE->getDataLayout();

    for (auto TmpI = I; TmpI != E; ++TmpI) {
        StructType *STy = TmpI.getStructTypeOrNull();
        *LastIndexIsVector = NULL;
        if (!STy)
            *LastIndexIsVector = dyn_cast<VectorType>(TmpI.getIndexedType());
        if (const ConstantInt *CI = dyn_cast<ConstantInt>(TmpI.getOperand())) {
            unsigned ElementIdx = CI->getZExtValue();
            if (STy)
                Total += TD.getStructLayout(STy)->getElementOffset(ElementIdx);
            else {
                ERRORIF(isa<GlobalValue>(TmpI.getOperand()));
                //Total += TD.getTypeAllocSize(cast<SequentialType>(Ty)->getElementType()) * ElementIdx;
                Total += TD.getTypeAllocSize(TmpI.getIndexedType()) * ElementIdx;
            }
        }
        else
            return -1;
    }
    return Total;
}

/*
 * Generate a string for the value represented by a GEP DAG
 */
static std::string printGEPExpression(const Value *Ptr, gep_type_iterator I, gep_type_iterator E)
{
    std::string cbuffer, amper = "&";
    const ConstantDataArray *CPA;
    int64_t Total = 0;
    VectorType *LastIndexIsVector = 0;
    const Constant *FirstOp = dyn_cast<Constant>(I.getOperand());
    bool expose = isAddressExposed(Ptr);
    std::string referstr = printOperand(Ptr, false);

    Total = getGEPOffset(&LastIndexIsVector, I, E);
    if (LastIndexIsVector)
        cbuffer += printType(PointerType::getUnqual(LastIndexIsVector->getElementType()), false, "", "((", ")(", false);
    if (trace_gep)
        printf("[%s:%d] referstr %s Total %ld\n", __FUNCTION__, __LINE__, referstr.c_str(), (unsigned long)Total);
    if (Total == -1) {
        printf("[%s:%d] non-constant offset referstr %s Total %ld\n", __FUNCTION__, __LINE__, referstr.c_str(), (unsigned long)Total);
    }
    if (I == E)
        return referstr;
    if (FirstOp && FirstOp->isNullValue()) {
        ++I;  // Skip the zero index.
        if (I == E) { // off the end of parameters
            // HACK HACK HACK HACK for 'fifo0'
            printf("[%s:%d] amper %s expose %d referstr %s\n", __FUNCTION__, __LINE__, amper.c_str(), expose, referstr.c_str());
            amper = "";
            referstr += "0";
        } else
        if (I != E && (I.getIndexedType())->isArrayTy())
            if (const ConstantInt *CI = dyn_cast<ConstantInt>(I.getOperand())) {
                uint64_t val = CI->getZExtValue();
                if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(Ptr))
                if (globalVar && !globalVar->getInitializer()->isNullValue()
                 && (CPA = dyn_cast<ConstantDataArray>(globalVar->getInitializer()))) {
                    ERRORIF(val || !CPA->isString());
                    referstr = printString(CPA->getAsString());
                }
                if (val)
                    referstr += '+' + utostr(val);
                amper = "";
                if (trace_gep)
                    printf("[%s:%d] expose %d referstr %s\n", __FUNCTION__, __LINE__, expose, referstr.c_str());
                ++I;     // we processed this index
            }
    }
    cbuffer += amper;
    for (; I != E; ++I) {
        if (const StructType *STy = I.getStructTypeOrNull()) {
            uint64_t foffset = cast<ConstantInt>(I.getOperand())->getZExtValue();
            std::string dot = MODULE_DOT;
            std::string fname = fieldName(STy, foffset);
            if (trace_gep)
                printf("[%s:%d] expose %d referstr %s cbuffer %s STy %s fname %s\n", __FUNCTION__, __LINE__, expose, referstr.c_str(), cbuffer.c_str(), STy->getName().str().c_str(), fname.c_str());
            if (!expose && referstr[0] == '&') {
                expose = true;
                referstr = referstr.substr(1);
            }
            if (expose)
                referstr += dot;
            else if (referstr == "this")
                referstr = "";
            else {
                std::string arrow = MODULE_ARROW;
                arrow = MODULE_DOT;
                if (referstr == "this") {
                    arrow = MODULE_ARROW;
                    referstr = "thisp";
                }
                else if (arrow == "->" || referstr.find(" ") != std::string::npos) {
                    // HACK: spaces mean "has expression inside"
                    referstr = "(" + referstr + ")";
                    arrow = MODULE_ARROW;
                }
                referstr += arrow;
            }
            cbuffer += referstr + fname;
        }
        else {
            Type *Ty = I.getIndexedType();
            if (trace_gep)
                printf("[%s:%d] expose %d referstr %s cbuffer %s array %d vector %d\n", __FUNCTION__, __LINE__, expose, referstr.c_str(), cbuffer.c_str(), Ty->isArrayTy(), Ty->isVectorTy());
            if (Ty->isArrayTy()) {
                if (referstr[0] == '&')
                    referstr = referstr.substr(1);
                cbuffer += referstr;
                //cbuffer += "[" + printOperand(I.getOperand(), false) + "]";
                cbuffer += printOperand(I.getOperand(), false);
            }
            else if (!Ty->isVectorTy()) {
                if (referstr[0] == '&')
                    referstr = referstr.substr(1);
                cbuffer += referstr;
                //cbuffer += "[" + printOperand(I.getOperand(), false) + "]";
                // HACK HACK HACK HACK: we append the offset for ivector.  lpm and precision tests have an i8* here.
                if (Ty !=  Type::getInt8PtrTy(globalMod->getContext()))
                    cbuffer += printOperand(I.getOperand(), false);
            }
            else {
                cbuffer += referstr;
                if (!isa<Constant>(I.getOperand()) || !cast<Constant>(I.getOperand())->isNullValue())
                    cbuffer += ")+(" + printOperand(I.getOperand(), false);
                cbuffer += "))";
            }
        }
        referstr = "";
    }
    cbuffer += referstr;
    if (trace_gep || Total == -1)
        printf("%s: return '%s'\n", __FUNCTION__, cbuffer.c_str());
    return cbuffer;
}

std::string getMethodName(const Function *func)
{
    std::string fname = func->getName();
    if (const StructType *targetSTy = findThisArgument(func))
    if (ClassMethodTable *targetTable = getClass(targetSTy))
        for (auto item: targetTable->method)
            if (item.second == func)
                return item.first;
    if (fname == "printf")
        return "";
    return "";
}

/*
 * Generate a string for a function/method call
 */
static std::string printCall(const Instruction *I)
{
    const CallInst *ICL = dyn_cast<CallInst>(I);
    const Function *func = ICL->getCalledFunction();
    std::string calledName = func->getName();
    std::string vout, sep, fname = getMethodName(func), prefix = MODULE_ARROW;
    CallSite CS(const_cast<Instruction *>(I));
    CallSite::arg_iterator AI = CS.arg_begin(), AE = CS.arg_end();
    if (!func) {
        printf("%s: not an instantiable call!!!! %s\n", __FUNCTION__, printOperand(*AI, false).c_str());
        I->dump();
        I->getParent()->getParent()->dump();
        parseError();
return "";
        exit(-1);
    }
    std::string pcalledFunction = printOperand(*AI++, false); // skips 'this' param
    if (pcalledFunction[0] == '&') {
        pcalledFunction = pcalledFunction.substr(1);
        //prefix = MODULE_DOT;
    }
    prefix = pcalledFunction + prefix;
    if (pcalledFunction == "this") {
        pcalledFunction = "";
        prefix = "";
    }
    if (trace_call || fname == "")
        printf("CALL: CALLER %s func %s[%p] pcalledFunction '%s' fname %s\n", globalMethodName.c_str(), calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
    if (fname == "") {
        fname = "[ERROR_" + calledName + "_ERROR]";
        //exit(-1);
    }
    if (calledName == "printf") {
        //printf("CALL: PRINTFCALLER %s func %s[%p] pcalledFunction '%s' fname %s\n", globalMethodName.c_str(), calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
        vout = "printf{" + pcalledFunction.substr(1, pcalledFunction.length()-2);
        sep = ",";
    }
    else {
        std::string methodName = prefix + fname;
        vout += methodName + "{";
    }
    auto FAI = func->arg_begin();
    for (FAI++; AI != AE; ++AI, FAI++) { // first param processed as pcalledFunction
        bool indirect = dyn_cast<PointerType>((*AI)->getType()) != NULL;
        if (auto *ins = dyn_cast<Instruction>(*AI)) {
            if (ins->getOpcode() == Instruction::GetElementPtr)
                indirect = true;
        }
        if (dyn_cast<Argument>(*AI))
            indirect = false;
        std::string parg = printOperand(*AI, indirect);
        vout += sep + prefix + FAI->getName().str() + ";" + parg;
        sep = ",";
    }
    return vout + "}";
}

std::string parenOperand(const Value *Operand)
{
    std::string temp = printOperand(Operand, false);
    int indent = 0;
    for (auto ch: temp)
        if (ch == '{')
            indent++;
        else if (ch == '}')
            indent--;
        else if (indent == 0 && !isalnum(ch) && ch != '$' && ch != '_')
            return "(" + temp + ")";
    return temp;
}

static void setCondition(BasicBlock *bb, int invert, Value *val)
{
    blockCondition[invert].val[bb] = val;
}

static Value *getACondition(BasicBlock *bb, int invert)
{
    if (Value *val = blockCondition[invert].val[bb])
        return val;
    if (Instruction *val = dyn_cast_or_null<Instruction>(blockCondition[1-invert].val[bb])) {
        BasicBlock *prevBB = val->getParent();
        Instruction *TI = bb->getTerminator();
        if (!TI) {
printf("[%s:%d] terminator not found!!\n", __FUNCTION__, __LINE__);
            bb->dump();
            exit(-1);
        }
        if (prevBB != bb) {
            prepareReplace(NULL, NULL);
            val = cloneTree(val, TI);
        }
        IRBuilder<> builder(bb);
        builder.SetInsertPoint(TI);
        setCondition(bb, invert, BinaryOperator::Create(Instruction::Xor,
           val, builder.getInt1(1), "invertCond", TI));
        return blockCondition[invert].val[bb];
    }
    return NULL;
}
static std::string getCondStr(BasicBlock *bb)
{
    if (Value *cond = getACondition(bb, 0))
        return printOperand(cond, false);
    return "";
}

/*
 * Generate a string for the value generated by an Instruction DAG
 */
std::string printOperand(const Value *Operand, bool Indirect)
{
    static int depth;
    std::string cbuffer;
    if (!Operand)
        return "";
    depth++;
    if (const Instruction *I = dyn_cast<Instruction>(Operand)) {
        std::string prefix;
        bool isAddressImplicit = isAddressExposed(Operand);
        if (Indirect && isAddressImplicit) {
            isAddressImplicit = false;
            Indirect = false;
        }
        if (Indirect)
            prefix = "*";
        if (isAddressImplicit)
            prefix = "&";  // Global variables are referenced as their addresses by llvm
        std::string vout;
        int opcode = I->getOpcode();
        if (trace_operand)
            printf("[%s:%d] before depth %d op %s\n", __FUNCTION__, __LINE__, depth, I->getOpcodeName());
        switch(opcode) {
        case Instruction::Call:
            vout += printCall(I);
            break;
        case Instruction::GetElementPtr: {
            const GetElementPtrInst *IG = dyn_cast<GetElementPtrInst>(I);
            vout = printGEPExpression(IG->getPointerOperand(), gep_type_begin(IG), gep_type_end(IG));
            break;
            }
        case Instruction::Load:
            vout = printOperand(I->getOperand(0), true);
            break;

        // Standard binary operators...
        case Instruction::Add: case Instruction::FAdd:
        case Instruction::Sub: case Instruction::FSub:
        case Instruction::Mul: case Instruction::FMul:
        case Instruction::UDiv: case Instruction::SDiv: case Instruction::FDiv:
        case Instruction::URem: case Instruction::SRem: case Instruction::FRem:
        case Instruction::Shl: case Instruction::LShr: case Instruction::AShr:
        // Logical operators...
        case Instruction::And: case Instruction::Or: case Instruction::Xor:
            assert(!I->getType()->isPointerTy());
            if (BinaryOperator::isNeg(I))
                vout += "-(" + printOperand(BinaryOperator::getNegArgument(cast<BinaryOperator>(I)), false) + ")";
            else if (BinaryOperator::isFNeg(I))
                vout += "-(" + printOperand(BinaryOperator::getFNegArgument(cast<BinaryOperator>(I)), false) + ")";
            else if (I->getOpcode() == Instruction::FRem) {
                if (I->getType() == Type::getFloatTy(I->getContext()))
                    vout += "fmodf(";
                else if (I->getType() == Type::getDoubleTy(I->getContext()))
                    vout += "fmod(";
                else  // all 3 flavors of long double
                    vout += "fmodl(";
                vout += printOperand(I->getOperand(0), false) + ", "
                     + printOperand(I->getOperand(1), false) + ")";
            } else
                vout += parenOperand(I->getOperand(0))
                     + " " + intmapLookup(opcodeMap, I->getOpcode()) + " "
                     + parenOperand(I->getOperand(1));
            break;

        // Convert instructions...
        case Instruction::SExt:
        case Instruction::FPTrunc: case Instruction::FPExt:
        case Instruction::FPToUI: case Instruction::FPToSI:
        case Instruction::UIToFP: case Instruction::SIToFP:
        case Instruction::IntToPtr: case Instruction::PtrToInt:
        case Instruction::AddrSpaceCast:
        case Instruction::Trunc: case Instruction::ZExt: case Instruction::BitCast:
            vout += printOperand(I->getOperand(0), false);
            break;

        // Other instructions...
        case Instruction::ICmp: case Instruction::FCmp: {
            const ICmpInst *CI = dyn_cast<ICmpInst>(I);
            vout += parenOperand(I->getOperand(0))
                 + " " + intmapLookup(predText, CI->getPredicate()) + " "
                 + parenOperand(I->getOperand(1));
            break;
            }
        case Instruction::PHI: {
            const PHINode *PN = dyn_cast<PHINode>(I);
            Value *prevCond = NULL;
            for (unsigned opIndex = 0, Eop = PN->getNumIncomingValues(); opIndex < Eop; opIndex++) {
                BasicBlock *inBlock = PN->getIncomingBlock(opIndex);
                std::string cStr = getCondStr(inBlock);
                if (cStr != "" && (opIndex != Eop - 1 || getACondition(inBlock, 1) != prevCond))
                    vout += cStr + " ? ";
                prevCond = getACondition(inBlock, 0);
                vout += printOperand(PN->getIncomingValue(opIndex), false);
                if (opIndex != Eop - 1)
                    vout += ":";
            }
            break;
            }
        case Instruction::Alloca:
            prefix = "";
            vout += GetValueName(I);
            break;
        default:
            printf("printOperand: Other opcode %d.=%s\n", opcode, I->getOpcodeName());
            I->getParent()->getParent()->dump();
            exit(1);
            break;
        }
        if (prefix == "*" && vout[0] == '&') {
            prefix = "";
            vout = vout.substr(1);
        }
        if (prefix == "")
            cbuffer += vout;
        else
            cbuffer += prefix + "(" + vout + ")";
        if (trace_operand)
             printf("[%s:%d] after depth %d op %s\n", __FUNCTION__, __LINE__, depth, I->getOpcodeName());
    }
    else {
        //we need pointer to pass struct params (PipeIn)
        const Constant* CPV = dyn_cast<Constant>(Operand);
        if (trace_operand)
            printf("[%s:%d] before depth %d noninst %p CPV %p\n", __FUNCTION__, __LINE__, depth, Operand, CPV);
        if (!CPV || isa<GlobalValue>(CPV))
            cbuffer += GetValueName(Operand);
        else {
            /* handle expressions */
            ERRORIF(isa<UndefValue>(CPV) && CPV->getType()->isSingleValueType()); /* handle 'undefined' */
            if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(CPV)) {
                cbuffer += "(";
                int op = CE->getOpcode();
                assert (op == Instruction::GetElementPtr);
                // used for character string args to printf()
                cbuffer += printGEPExpression(CE->getOperand(0), gep_type_begin(CPV), gep_type_end(CPV)) +  ")";
            }
            else if (const ConstantInt *CI = dyn_cast<ConstantInt>(CPV)) {
                char temp[100];
                Type* Ty = CI->getType();
                temp[0] = 0;
                if (Ty == Type::getInt1Ty(CPV->getContext()))
                    cbuffer += CI->getZExtValue() ? "1" : "0";
                else if (Ty == Type::getInt32Ty(CPV->getContext()) || Ty->getPrimitiveSizeInBits() > 32)
                    sprintf(temp, "%ld", (long)CI->getSExtValue());
                else if (CI->isMinValue(true))
                    sprintf(temp, "%ld", (long)CI->getZExtValue());//  'u';
                else
                    sprintf(temp, "%ld", (long)CI->getSExtValue());
                cbuffer += temp;
            }
            else
                ERRORIF(1); /* handle structured types */
        }
    }
    if (trace_operand)
        printf("[%s:%d] depth %d return '%s'\n", __FUNCTION__, __LINE__, depth, cbuffer.c_str());
    depth--;
    return cbuffer;
}

static std::list<Instruction *> preCopy;
// This code recursively expands an expression tree that has PHI instructions
// into a list of trees that for each possible incoming value to the PHI.
// It is used when computing guard expressions to calculate the 'AND' of all
// possible targets (ignoring which ones are actually going to be used
// dynamically).
static Instruction *defactorTree(Instruction *insertPoint, Instruction *top, Instruction *arg)
{
    if (const PHINode *PN = dyn_cast<PHINode>(arg)) {
        for (unsigned opIndex = 1, Eop = PN->getNumIncomingValues(); opIndex < Eop; opIndex++) {
            prepareReplace(arg, PN->getIncomingValue(opIndex));
            preCopy.push_back(cloneTree(top, insertPoint));
        }
        return dyn_cast<Instruction>(PN->getIncomingValue(0));
    }
    else
        for (unsigned int i = 0; i < arg->getNumOperands(); i++) {
            if (Instruction *param = dyn_cast<Instruction>(arg->getOperand(i))) {
                Instruction *ret = defactorTree(insertPoint, top, param);
                if (ret) {
                    arg->setOperand(i, ret);
                    recursiveDelete(param);
                }
            }
        }
    return NULL; // nothing to expand
}
static Instruction *expandTreeOptions(Instruction *insertPoint, const Instruction *I, Function *func)
{
    std::list<Instruction *> postCopy;
    preCopy.clear();
    Instruction *retItem = NULL;
    prepareClone(insertPoint, I->getParent()->getParent());
    Value *new_thisp = I->getOperand(0);
    if (Instruction *orig_thisp = dyn_cast<Instruction>(new_thisp))
        new_thisp = cloneTree(orig_thisp, insertPoint);
    preCopy.push_back(dyn_cast<Instruction>(new_thisp));
    for (auto item: preCopy) {
        defactorTree(insertPoint, item, item);
        postCopy.push_back(item);
    }
    for (auto item: postCopy) {
        Value *Params[] = {item};
        IRBuilder<> builder(insertPoint->getParent());
        builder.SetInsertPoint(insertPoint);
        CallInst *newCall = builder.CreateCall(func, ArrayRef<Value*>(Params, 1));
        //newCall->addAttribute(AttributeSet::ReturnIndex, Attribute::ZExt);
        if (retItem)
            retItem = BinaryOperator::Create(Instruction::And, retItem, newCall, "newand", insertPoint);
        else
            retItem = newCall;
    }
    return retItem;
}

/*
 * Add another condition to a guard function.
 */
static Instruction *recClean(Instruction *arg)
{
    int opcode = arg->getOpcode();
    for (unsigned i = 0, e = arg->getNumOperands(); i != e; ++i) {
        if (Instruction *op = dyn_cast<Instruction>(arg->getOperand(i))) {
            Instruction *newOp = recClean(op);
            if (!newOp) {
                if (opcode == Instruction::Or || opcode == Instruction::And) {
                    if (Instruction *otherOp = dyn_cast<Instruction>(arg->getOperand(1-i))) {
                        Instruction *onewOp = recClean(otherOp);
//printf("[%s:%d] AND/OR replace i=%d newOp %p onewOp %p\n", __FUNCTION__, __LINE__, i, newOp, onewOp);
//op->dump();
//otherOp->dump();
                        if (onewOp)
                            return onewOp;
                    }
                }
                return NULL;
            }
            if (newOp != op) {
                op->replaceAllUsesWith(newOp);
                recursiveDelete(op);
            }
        }
        else if (Argument *inv = dyn_cast<Argument>(arg->getOperand(i))) {
//printf("[%s:%d] inv %p begin %p\n", __FUNCTION__, __LINE__, inv, &*arg->getParent()->getParent()->arg_begin());
//arg->dump();
            if (inv != arg->getParent()->getParent()->arg_begin()) {
//printf("[%s:%d] ARGNULL\n", __FUNCTION__, __LINE__);
                return NULL;
            }
        }
    }
    return arg;
}

static void addGuard(Instruction *argI, Function *func, Function *currentFunction)
{
    /* get my function's guard function */
    Function *parentRDYName = ruleRDYFunction[currentFunction];
    assert (parentRDYName && func);
    TerminatorInst *TI = parentRDYName->begin()->getTerminator();
    /* make a call to the guard being promoted */
    Instruction *newI = expandTreeOptions(TI, argI, func);
    /* if the promoted guard is in an 'if' block, 'or' with inverted condition of block */
    if (Instruction *bcond = dyn_cast_or_null<Instruction>(getACondition(argI->getParent(), 1))) { // get inverted condition, if any
        prepareReplace(argI->getParent()->getParent()->arg_begin(), TI->getParent()->getParent()->arg_begin());
        newI = BinaryOperator::Create(Instruction::Or, newI, cloneTree(bcond,TI), "newor", TI);
    }
    /* get existing return value from my function's guard */
    Value *cond = TI->getOperand(0);
    const ConstantInt *CI = dyn_cast<ConstantInt>(cond);
    if (!CI || !CI->getType()->isIntegerTy(1) || !CI->getZExtValue())
        newI = BinaryOperator::Create(Instruction::And, cond, newI, "newand", TI);
        // 'And' return value into condition
//printf("[%s:%d] condition '%s'\n", __FUNCTION__, __LINE__, printOperand(newI, false).c_str());
//parentRDYName->dump();
    Instruction *repNewI = recClean(newI);
    TI->setOperand(0, repNewI); /* replace 'return' expression */
    if (repNewI != newI)
        recursiveDelete(newI);
}

// Preprocess the body rules, moving items to RDY() and ENA()
static void processPromote(Function *currentFunction)
{
restart:
    for (auto BI = currentFunction->begin(), BE = currentFunction->end(); BI != BE; BI++) {
        for (auto IIb = BI->begin(), IE = BI->end(); IIb != IE;) {
            auto INEXT = std::next(BasicBlock::iterator(IIb));
            Instruction *II = &*IIb;
            switch (II->getOpcode()) {
            case Instruction::Call: {
                Function *func = dyn_cast<Function>(dyn_cast<CallInst>(II)->getCalledValue());
                Function *calledFunctionGuard = ruleRDYFunction[func];
                if (trace_hoist)
                    printf("HOIST: CALLER %s calling '%s' guard %p\n", currentFunction->getName().str().c_str(), func->getName().str().c_str(), calledFunctionGuard);
                if (calledFunctionGuard)
                    addGuard(II, calledFunctionGuard, currentFunction);
                break;
                }
            case Instruction::Br: {
                // BUG BUG BUG -> combine the condition for the current block with the getConditions for this instruction
                const BranchInst *BI = dyn_cast<BranchInst>(II);
                if (BI && BI->isConditional()) {
                    //printf("[%s:%d] condition %s [%p, %p]\n", __FUNCTION__, __LINE__, printOperand(BI->getCondition(), false).c_str(), BI->getSuccessor(0), BI->getSuccessor(1));
                    setCondition(BI->getSuccessor(0), 0, BI->getCondition()); // 'true' condition
                    setCondition(BI->getSuccessor(1), 1, BI->getCondition()); // 'inverted' condition
                }
                else if (isa<IndirectBrInst>(II)) {
                    printf("[%s:%d] indirect\n", __FUNCTION__, __LINE__);
                    for (unsigned i = 0, e = II->getNumOperands(); i != e; ++i) {
                        printf("[%d] = %s\n", i, printOperand(II->getOperand(i), false).c_str());
                    }
                }
                else {
                    //printf("[%s:%d] BRUNCOND %p\n", __FUNCTION__, __LINE__, BI->getSuccessor(0));
                }
                break;
                }
            case Instruction::Switch: {
                SwitchInst* SI = cast<SwitchInst>(II);
                Value *switchIndex = SI->getCondition();
                Type  *swType = switchIndex->getType();
                //BasicBlock *defaultBB = SI->getDefaultDest();
                for (SwitchInst::CaseIt CI = SI->case_begin(), CE = SI->case_end(); CI != CE; ++CI) {
                    BasicBlock *caseBB = CI->getCaseSuccessor();
                    int64_t val = CI->getCaseValue()->getZExtValue();
                    printf("[%s:%d] [%ld] = %s\n", __FUNCTION__, __LINE__, val, caseBB?caseBB->getName().str().c_str():"NONE");
                    if (getCondStr(caseBB) == "") { // 'true' condition
                        IRBuilder<> cbuilder(caseBB);
                        Instruction *TI = caseBB->getTerminator();
                        Value *myIndex = switchIndex;
                        if (Instruction *expr = dyn_cast<Instruction>(switchIndex)) {
                            prepareClone(TI, II->getParent()->getParent());
                            myIndex = cloneTree(expr, TI);
                        }
                        cbuilder.SetInsertPoint(TI);
                        Value *cmp = cbuilder.CreateICmpEQ(myIndex, ConstantInt::get(swType, val));
                        setCondition(caseBB, 0, cmp);
                    }
                }
                //printf("[%s:%d] after switch\n", __FUNCTION__, __LINE__);
                //II->getParent()->getParent()->dump();
                break;
                }
            case Instruction::GetElementPtr:
                // Expand out index expression references
                if (II->getNumOperands() == 2)
                if (Instruction *switchIndex = dyn_cast<Instruction>(II->getOperand(1))) {
                    int Values_size = 2;
                    if (Instruction *ins = dyn_cast<Instruction>(II->getOperand(0))) {
                        if (PointerType *PTy = dyn_cast<PointerType>(ins->getOperand(0)->getType()))
                        if (StructType *STy = dyn_cast<StructType>(PTy->getElementType())) {
                            int Idx = 0, eleIndex = -1;
                            if (const ConstantInt *CI = dyn_cast<ConstantInt>(ins->getOperand(2)))
                                eleIndex = CI->getZExtValue();
                            for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++)
                                if (Idx == eleIndex)
                                if (ClassMethodTable *table = getClass(STy))
                                    if (table->replaceType[Idx]) {
                                        Values_size = table->replaceCount[Idx];
printf("[%s:%d] get dyn size (static not handled) %d\n", __FUNCTION__, __LINE__, Values_size);
if (Values_size < 0 || Values_size > 100) Values_size = 2;
                                        //II->getParent()->dump();
                                    }
                        }
                        ins->getOperand(0)->dump();
                    }
                    II->getOperand(0)->dump();
                    BasicBlock *afterswitchBB = BI->splitBasicBlock(II, "afterswitch");
                    IRBuilder<> afterBuilder(afterswitchBB);
                    afterBuilder.SetInsertPoint(II);
                    // Build Switch instruction in starting block
                    IRBuilder<> startBuilder(&*BI);
                    startBuilder.SetInsertPoint(BI->getTerminator());
                    BasicBlock *lastCaseBB = BasicBlock::Create(BI->getContext(), "lastcase", currentFunction, afterswitchBB);
                    SwitchInst *switchInst = startBuilder.CreateSwitch(switchIndex, lastCaseBB, Values_size - 1);
                    BI->getTerminator()->eraseFromParent();
                    // Build PHI in end block
                    PHINode *phi = afterBuilder.CreatePHI(II->getType(), Values_size, "phi");
                    // Add all of the 'cases' to the switch instruction.
                    for (int caseIndex = 0; caseIndex < Values_size; ++caseIndex) {
                        ConstantInt *caseInt = startBuilder.getInt64(caseIndex);
                        BasicBlock *caseBB = lastCaseBB;
                        if (caseIndex != Values_size - 1) { // already created a block for 'default'
                            caseBB = BasicBlock::Create(BI->getContext(), "switchcase", currentFunction, afterswitchBB);
                            switchInst->addCase(caseInt, caseBB);
                        }
                        IRBuilder<> cbuilder(caseBB);
                        cbuilder.CreateBr(afterswitchBB);
                        prepareReplace(NULL, NULL);
                        Instruction *val = cloneTree(II, caseBB->getTerminator());
                        val->setOperand(1, caseInt);
                        phi->addIncoming(val, caseBB);
                    }
                    II->replaceAllUsesWith(phi);
                    recursiveDelete(II);
                    goto restart;  // the instruction INEXT is no longer in the block BI
                }
                break;
            }
            IIb = INEXT;
        }
    }
}

/*
 * Walk all BasicBlocks for a Function, generating strings for Instructions
 * that are not inlinable.
 */
static void processClass(ClassMethodTable *table)
{
    for (auto FI : table->method) {
        globalMethodName = FI.first;
        const Function *func = FI.second;
        // promote guards from contained calls to be guards for this function
        processPromote(const_cast<Function *>(func));
        NextAnonValueNumber = 0;
        if (trace_function || trace_call)
            printf("PROCESSING %s %s\n", func->getName().str().c_str(), FI.first.c_str());
        /* Gather data for top level instructions in each basic block. */
        std::string temp, valsep;
        for (auto BI = func->begin(), BE = func->end(); BI != BE; ++BI) {
            std::string tempCond = getCondStr(const_cast<BasicBlock *>(&*BI));
            auto appendList = [&](int listIndex, std::string item) -> void {
                  if (tempCond == "")
                      funcMetaMap[func].list[listIndex][item].clear();
                  funcMetaMap[func].list[listIndex][item].insert(tempCond);
              };
            for (auto IIb = BI->begin(), IE = BI->end(); IIb != IE;IIb++) {
                const Instruction *II = &*IIb;
                switch(II->getOpcode()) {
                case Instruction::Load:
                    ERRORIF(dyn_cast<LoadInst>(II)->isVolatile());
                    if (II->getType()->getTypeID() != Type::PointerTyID
                     && !isAlloca(II->getOperand(0)) && !dyn_cast<Argument>(II->getOperand(0)))
                        appendList(MetaRead, printOperand(II->getOperand(0), true));
                    break;
                case Instruction::Store: {
                    const StoreInst *SI = cast<StoreInst>(II);
                    std::string value = printOperand(SI->getOperand(0), false);
                    std::string dest = printOperand(SI->getPointerOperand(), true);
                    if (dest[0] == '&')
                        dest = dest.substr(1);
                    storeList[func].push_back(StoreListElement{dest, value, tempCond,
                         isAlloca(SI->getPointerOperand())});
                    std::string pdest = printOperand(SI->getPointerOperand(), true);
                    if (pdest[0] == '&')
                        pdest = pdest.substr(1);
                    if (!isAlloca(SI->getPointerOperand()))
                        appendList(MetaWrite, pdest);
                    printOperand(II->getOperand(0), false); // force evaluation to get metadata
                    break;
                    }
                case Instruction::Ret:
                    if (!II->getNumOperands())
                        break;
                    functionList[func].push_back(II);
                    temp += valsep;
                    valsep = "";
                    if (tempCond != "")
                        temp += tempCond + " ? ";
                    valsep = " : ";
                    temp += printOperand(II->getOperand(0), false);
                    break;
                case Instruction::Call: { // can have value
                    if (cast<CallInst>(II)->getCalledFunction()->getName() == "printf")
                        break;
                    std::string condStr, value = printCall(II);
                    if (tempCond != "")
                        condStr = " & " + tempCond;
                    appendList(MetaInvoke, value.substr(0,value.find("{")));
                    if (II->getType() == Type::getVoidTy(II->getContext()))
                        callList[func].push_back(CallListElement{value, condStr,
                            isActionMethod(cast<CallInst>(II)->getCalledFunction())});
                    break;
                    }
                }
            }
        }
        table->guard[func] = temp;
    }
}

static std::list<const StructType *> structSeq;
static std::map<std::string, const StructType *> structAlpha;

static void getDepend(const StructType *STy)
{
    std::map<std::string, const StructType *> structTemp;
    if (!STy->hasName() || STy->getName().substr(0, 7) == "emodule")
        return;
    std::string name = getStructName(STy);

    if (!isInterface(STy))
    if (strncmp(STy->getName().str().c_str(), "class.std::", 11) // don't generate anything for std classes
     && strncmp(STy->getName().str().c_str(), "struct.std::", 12)) {
        ClassMethodTable *table = getClass(STy);
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            const Type *element = *I;
            if (table)
            if (const Type *newType = table->replaceType[Idx])
                element = newType;
            if (auto iSTy = dyn_cast<StructType>(element))
                structTemp[getStructName(iSTy)] = iSTy;
        }
        for (auto FI : table->method) {
            const Function *func = FI.second;
            auto AI = func->arg_begin(), AE = func->arg_end();
            if (const StructType *iSTy = dyn_cast<StructType>(func->getReturnType()))
                structTemp[getStructName(iSTy)] = iSTy;
            AI++;
            for (; AI != AE; ++AI) {
                Type *element = AI->getType();
                if (auto PTy = dyn_cast<PointerType>(element))
                    element = PTy->getElementType();
                if (const StructType *iSTy = dyn_cast<StructType>(element))
                    structTemp[getStructName(iSTy)] = iSTy;
            }
        }
    }
    for (auto element: structTemp) {
         if (structAlpha[element.first])
             getDepend(element.second);
         if (structAlpha[element.first]) {
             structSeq.push_back(element.second);
             structAlpha[element.first] = NULL;
         }
    }
    if (structAlpha[name]) {
        structSeq.push_back(STy);
        structAlpha[name] = NULL;
    }
}

void generateClasses(FILE *OStrV, FILE *OStrVH)
{
    for (auto current : classCreate)
        structAlpha[getStructName(current.first)] = current.first;
    for (auto item : structAlpha)
        if (item.second)
            getDepend(item.second);
    for (auto STy : structSeq) {
        if (STy->getName().substr(0, 6) == "module") {
            processClass(getClass(STy));
            // now generate the verilog header file '.vh'
            metaGenerate(STy, OStrVH);
            // Only generate verilog for modules derived from Module
            generateModuleDef(STy, OStrV);
        }
    }
}
