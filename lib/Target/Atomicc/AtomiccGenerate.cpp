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
std::map<const StructType *,ClassMethodTable *> classCreate;
static unsigned NextTypeID;

static std::map<const Value *, std::string> allocaMap;
static DenseMap<const Value*, unsigned> AnonValueNumbers;
static unsigned NextAnonValueNumber;
static DenseMap<const StructType*, unsigned> UnnamedStructIDs;
Module *globalMod;
std::map<const Function *,std::list<StoreInst *>> storeList;
std::map<const Function *,std::list<Instruction *>> functionList;
std::map<const Function *,std::list<Instruction *>> callList;
std::map<const Function *,std::list<Instruction *>> declareList;
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
bool isAlloca(Value *arg)
{
    if (GetElementPtrInst *IG = dyn_cast_or_null<GetElementPtrInst>(arg))
        arg = dyn_cast<Instruction>(IG->getPointerOperand());
    if (Instruction *source = dyn_cast_or_null<Instruction>(arg))
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
    unsigned int subs = 0;
    int idx = ind;
    while (idx-- > 0) {
        while (subs < STy->structFieldMap.length() && STy->structFieldMap[subs] != ',') {
            if (STy->structFieldMap[subs] == '/')
                return "";
            subs++;
        }
        subs++;
    }
    if (subs >= STy->structFieldMap.length() || STy->structFieldMap[subs] == '/')
        return "";
    std::string ret = STy->structFieldMap.substr(subs);
    idx = ret.find(',');
    if (idx >= 0)
        ret = ret.substr(0,idx);
    return ret;
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
    ClassMethodTable *table = classCreate[STy];
    //ClassMethodTable *atable = classCreate[ActSTy];
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        Type *element = *I;
        if (table)
            if (Type *newType = table->replaceType[Idx])
                element = newType;
        std::string fname = fieldName(STy, Idx);
        if (const StructType *iSTy = dyn_cast<StructType>(element)) {
            if (fname == "")
                checkClass(iSTy, ActSTy);
        }
    }
}

void getClass(const StructType *STy)
{
    if (!classCreate[STy]) {
        classCreate[STy] = new ClassMethodTable;
        classCreate[STy]->STy = STy;
        checkClass(STy, STy);
    }
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
const StructType *findThisArgument(Function *func)
{
    return findThisArgumentType(func->getType(), false);
}

/*
 * Output type declarations.  Note that each case in the switch statement
 * is different for verilog and cpp.
 */
std::string printType(Type *Ty, bool isSigned, std::string NameSoFar, std::string prefix, std::string postfix, bool ptr)
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
        FunctionType *FTy = cast<FunctionType>(Ty);
        Type *retType = FTy->getReturnType();
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
        ArrayType *ATy = cast<ArrayType>(Ty);
        unsigned len = ATy->getNumElements();
        if (len == 0) len = 1;
        cbuffer += printType(ATy->getElementType(), false, "", "", "", false) + NameSoFar + "[" + utostr(len) + "]";
        break;
        }
    case Type::PointerTyID: {
        PointerType *PTy = cast<PointerType>(Ty);
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
        Type *Ty = TmpI.getIndexedType();
        *LastIndexIsVector = dyn_cast<VectorType>(Ty);
        if (const ConstantInt *CI = dyn_cast<ConstantInt>(TmpI.getOperand())) {
            if (StructType *STy = dyn_cast<StructType>(Ty))
                Total += TD.getStructLayout(STy)->getElementOffset(CI->getZExtValue());
            else {
                ERRORIF(isa<GlobalValue>(TmpI.getOperand()));
                Total += TD.getTypeAllocSize(cast<SequentialType>(Ty)->getElementType()) * CI->getZExtValue();
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
static std::string printGEPExpression(Value *Ptr, gep_type_iterator I, gep_type_iterator E)
{
    std::string cbuffer, sep = " ", amper = "&";
    ConstantDataArray *CPA;
    int64_t Total = 0;
    VectorType *LastIndexIsVector = 0;
    Constant *FirstOp = dyn_cast<Constant>(I.getOperand());
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
        if (I == E) {
            // HACK HACK HACK HACK for 'fifo0'
            printf("[%s:%d] amper %s expose %d referstr %s\n", __FUNCTION__, __LINE__, amper.c_str(), expose, referstr.c_str());
            (I.getIndexedType())->dump();
            amper = "";
            referstr += "0";
        } else
        if (I != E && (I.getIndexedType())->isArrayTy())
            if (const ConstantInt *CI = dyn_cast<ConstantInt>(I.getOperand())) {
                uint64_t val = CI->getZExtValue();
                if (GlobalVariable *globalVar = dyn_cast<GlobalVariable>(Ptr))
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
        Type *Ty = I.getIndexedType();
        if (StructType *STy = dyn_cast<StructType>(Ty)) {
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
            if (trace_gep)
                printf("[%s:%d] expose %d referstr %s cbuffer %s array %d vector %d\n", __FUNCTION__, __LINE__, expose, referstr.c_str(), cbuffer.c_str(), (Ty)->isArrayTy(), (Ty)->isVectorTy());
            if ((Ty)->isArrayTy()) {
                if (referstr[0] == '&')
                    referstr = referstr.substr(1);
                cbuffer += referstr;
                //cbuffer += "[" + printOperand(I.getOperand(), false) + "]";
                cbuffer += printOperand(I.getOperand(), false);
            }
            else if (!(Ty)->isVectorTy()) {
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
        printf("%s: return %s\n", __FUNCTION__, cbuffer.c_str());
    return cbuffer;
}

static ClassMethodTable *globalClassTable;
static Function *globalProcessFunction;

static void appendList(int listIndex, BasicBlock *cond, std::string item)
{
    if (globalProcessFunction) {
        Value *val = getCondition(cond, 0);
        if (!val)
            funcMetaMap[globalProcessFunction].list[listIndex][item].clear();
        for (auto condIter: funcMetaMap[globalProcessFunction].list[listIndex][item])
            if (!condIter || condIter == val)
                return;
        funcMetaMap[globalProcessFunction].list[listIndex][item].push_back(val);
    }
}

std::string getMethodName(Function *func)
{
    std::string fname = func->getName();
    if (const StructType *targetSTy = findThisArgument(func))
    if (ClassMethodTable *targetTable = classCreate[targetSTy])
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
std::string printCall(Instruction *I)
{
    std::string vout, sep;
    CallInst *ICL = dyn_cast<CallInst>(I);
    Function *func = ICL->getCalledFunction();
    std::string fname = getMethodName(func);
    CallSite CS(I);
    CallSite::arg_iterator AI = CS.arg_begin(), AE = CS.arg_end();
    if (!func) {
        printf("%s: not an instantiable call!!!! %s\n", __FUNCTION__, printOperand(*AI, false).c_str());
        I->dump();
        I->getParent()->getParent()->dump();
        parseError();
return "";
        exit(-1);
    }
    auto FAI = func->arg_begin();
    std::string pcalledFunction = printOperand(*AI++, false); // skips 'this' param
    std::string prefix = MODULE_ARROW;
    if (pcalledFunction[0] == '&') {
        pcalledFunction = pcalledFunction.substr(1);
        prefix = MODULE_DOT;
    }
    prefix = pcalledFunction + prefix;
    if (pcalledFunction == "this") {
        pcalledFunction = "";
        prefix = "";
    }
    std::string calledName = func->getName();
    if (trace_call)
        printf("CALL: CALLER %s func %s[%p] pcalledFunction '%s' fname %s\n", globalMethodName.c_str(), calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
    if (fname == "") {
        printf("CALL: CALLER %s func %s[%p] pcalledFunction '%s' fname %s missing\n", globalMethodName.c_str(), calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
        //return "caller_error";
        fname = "[ERROR_" + calledName + "_ERROR]";
        //exit(-1);
    }
    if (calledName == "printf") {
        //printf("CALL: PRINTFCALLER %s func %s[%p] pcalledFunction '%s' fname %s\n", globalMethodName.c_str(), calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
        vout = "printf(" + pcalledFunction.substr(1, pcalledFunction.length()-2);
        sep = ", ";
    }
    else {
        std::string methodName = prefix + fname;
        if (isActionMethod(func))
            globalClassTable->muxEnableList.push_back(MuxEnableEntry{globalMethodName + "_internal", I->getParent(), methodName});
        else
            vout += methodName;
        appendList(MetaInvoke, I->getParent(), methodName);
    }
    for (FAI++; AI != AE; ++AI, FAI++) { // first param processed as pcalledFunction
        bool indirect = dyn_cast<PointerType>((*AI)->getType()) != NULL;
        if (auto *ins = dyn_cast<Instruction>(*AI)) {
            if (ins->getOpcode() == Instruction::GetElementPtr)
                indirect = true;
        }
        if (dyn_cast<Argument>(*AI))
            indirect = false;
        std::string parg = printOperand(*AI, indirect);
        globalClassTable->muxValueList[prefix + FAI->getName().str()]
            .push_back(MuxValueEntry{globalMethodName + "_internal", I->getParent(), parg});
        sep = ", ";
    }
    return vout;
}

std::string parenOperand(Value *Operand)
{
    std::string temp = printOperand(Operand, false);
    for (auto ch: temp)
        if (!isalnum(ch) && ch != '$' && ch != '_')
            return "(" + temp + ")";
    return temp;
}

/*
 * Generate a string for the value generated by an Instruction DAG
 */
std::string printOperand(Value *Operand, bool Indirect)
{
    static int depth;
    std::string cbuffer;
    if (!Operand)
        return "";
    depth++;
    if (Instruction *I = dyn_cast<Instruction>(Operand)) {
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
            GetElementPtrInst *IG = dyn_cast<GetElementPtrInst>(I);
            vout = printGEPExpression(IG->getPointerOperand(), gep_type_begin(IG), gep_type_end(IG));
            break;
            }
        case Instruction::Load: {
            vout = printOperand(I->getOperand(0), true);
            if (I->getType()->getTypeID() != Type::PointerTyID && !isAlloca(I->getOperand(0))
             && !dyn_cast<Argument>(I->getOperand(0)))
                appendList(MetaRead, I->getParent(), vout);
            break;
            }

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
            ICmpInst *CI = dyn_cast<ICmpInst>(I);
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
                Value *opCond = getCondition(inBlock, 0);
                if (opIndex != Eop - 1 || getCondition(inBlock, 1) != prevCond) {
                    std::string cStr = printOperand(opCond, false);
                    if (cStr != "")
                        vout += cStr + " ? ";
                }
                vout += printOperand(PN->getIncomingValue(opIndex), false);
                if (opIndex != Eop - 1)
                    vout += ":";
                prevCond = opCond;
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
        Constant* CPV = dyn_cast<Constant>(Operand);
        if (trace_operand)
            printf("[%s:%d] before depth %d noninst %p CPV %p\n", __FUNCTION__, __LINE__, depth, Operand, CPV);
        if (!CPV || isa<GlobalValue>(CPV))
            cbuffer += GetValueName(Operand);
        else {
            /* handle expressions */
            ERRORIF(isa<UndefValue>(CPV) && CPV->getType()->isSingleValueType()); /* handle 'undefined' */
            if (ConstantExpr *CE = dyn_cast<ConstantExpr>(CPV)) {
                cbuffer += "(";
                int op = CE->getOpcode();
                assert (op == Instruction::GetElementPtr);
                // used for character string args to printf()
                cbuffer += printGEPExpression(CE->getOperand(0), gep_type_begin(CPV), gep_type_end(CPV)) +  ")";
            }
            else if (ConstantInt *CI = dyn_cast<ConstantInt>(CPV)) {
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
        printf("[%s:%d] depth %d return %s\n", __FUNCTION__, __LINE__, depth, cbuffer.c_str());
    depth--;
    return cbuffer;
}

/*
 * Walk all BasicBlocks for a Function, generating strings for Instructions
 * that are not inlinable.
 */
static void processClass(ClassMethodTable *table)
{
    globalClassTable = table;
    for (auto FI : table->method) {
        globalMethodName = FI.first;
        Function *func = FI.second;
        globalProcessFunction = func;
        NextAnonValueNumber = 0;
        if (trace_function || trace_call)
            printf("PROCESSING %s\n", func->getName().str().c_str());
        /* Gather data for top level instructions in each basic block. */
        std::string temp, valsep;
        for (auto BI = func->begin(), BE = func->end(); BI != BE; ++BI) {
            for (auto IIb = BI->begin(), IE = BI->end(); IIb != IE;IIb++) {
                Instruction *II = &*IIb;
                switch(II->getOpcode()) {
                case Instruction::Load:
                    ERRORIF(dyn_cast<LoadInst>(II)->isVolatile());
                    break;
                case Instruction::Store: {
                    StoreInst *SI = cast<StoreInst>(II);
                    storeList[func].push_back(SI);
                    std::string pdest = printOperand(SI->getPointerOperand(), true);
                    if (pdest[0] == '&')
                        pdest = pdest.substr(1);
                    if (!isAlloca(SI->getPointerOperand()))
                        appendList(MetaWrite, II->getParent(), pdest);
                    (void)printOperand(II->getOperand(0), false); // force evaluation to get metadata
                    break;
                }
                case Instruction::Ret:
                    if (II->getNumOperands() != 0) {
                        functionList[func].push_back(II);
                        temp += valsep;
                        valsep = "";
                        if (Value *opCond = getCondition(II->getParent(), 0))
                            temp += printOperand(opCond, false) + " ? ";
                        valsep = " : ";
                        temp += printOperand(II->getOperand(0), false);
                    }
                    break;
                case Instruction::Alloca:
                    declareList[func].push_back(II);
                    break;
                case Instruction::Call: // can have value
                    if (II->getType() == Type::getVoidTy(II->getContext())) {
                        callList[func].push_back(II);
                        printCall(II);   // force evaluation to get metadata and side effects....
                    }
                    break;
                }
            }
        }
        table->guard[func] = temp;
    }
    globalClassTable = NULL;
    globalProcessFunction = NULL;
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
        ClassMethodTable *table = classCreate[STy];
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            Type *element = *I;
            if (table)
            if (Type *newType = table->replaceType[Idx])
                element = newType;
            if (auto iSTy = dyn_cast<StructType>(element))
                structTemp[getStructName(iSTy)] = iSTy;
        }
        for (auto FI : table->method) {
            Function *func = FI.second;
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
        //if (!isInterface(current.first))
        structAlpha[getStructName(current.first)] = current.first;
    for (auto item : structAlpha)
        if (item.second)
            getDepend(item.second);
    for (auto STy : structSeq) {
        ClassMethodTable *table = classCreate[STy];
        processClass(table);
        std::string temp;
        getClass(STy);
        temp = STy->getName();
        if (temp.substr(0, 6) == "module") {
            // now generate the verilog header file '.vh'
            metaGenerate(STy, OStrVH);
            // Only generate verilog for modules derived from Module
            generateModuleDef(STy, OStrV);
        }
    }
}
