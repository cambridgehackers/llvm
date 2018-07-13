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
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"

using namespace llvm;

#include "AtomiccDecl.h"

static int trace_function;//=1;
static int trace_call;//=1;
static int trace_gep;//=1;
static int trace_operand;//=1;
static std::map<const StructType *,ClassMethodTable *> classCreate;
static unsigned NextTypeID;
static std::string globalMethodName;

static DenseMap<const Value*, unsigned> AnonValueNumbers;
static unsigned NextAnonValueNumber;
static DenseMap<const StructType*, unsigned> UnnamedStructIDs;
Module *globalMod;

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
typedef struct {
    bool invert;
    std::string cond;
    const BasicBlock *from;
} BlockCondItem;

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

static bool isAlloca(const Value *arg)
{
    if (const GetElementPtrInst *IG = dyn_cast_or_null<GetElementPtrInst>(arg))
        arg = dyn_cast<Instruction>(IG->getPointerOperand());
    if (const CastInst *IG = dyn_cast_or_null<CastInst>(arg))
        arg = dyn_cast<Instruction>(IG->getOperand(0));
    if (const GetElementPtrInst *IG = dyn_cast_or_null<GetElementPtrInst>(arg))
        arg = dyn_cast<Instruction>(IG->getPointerOperand());
    if (const Instruction *source = dyn_cast_or_null<Instruction>(arg))
    if (source->getOpcode() == Instruction::Alloca)
            return true;
    return false;
}
/*
 * Return the name of the 'ind'th field of a StructType.
 * This code depends on a modification to llvm/clang that generates structFieldMap.
 */
std::string fieldName(const StructType *STy, uint64_t ind)
{
    return getClass(STy)->fieldName[ind].name;
}

bool isInterface(const StructType *STy)
{
    return STy && startswith(getClass(STy)->IR->name, "l_ainterface");
}

bool isActionMethod(const Function *func)
{
    return (func->getReturnType() == Type::getVoidTy(func->getContext()));
}

static void checkClass(const StructType *STy, const StructType *ActSTy)
{
    ClassMethodTable *table = getClass(STy);
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

static std::string legacygetStructName(const StructType *STy)
{
    assert(STy);
    getClass(STy);
    if (!STy->isLiteral() && !STy->getName().empty()) {
        std::string temp = STy->getName().str();
        if (startswith(temp, "emodule"))
            temp = temp.substr(1);
        return CBEMangle("l_" + temp);
    }
    if (!UnnamedStructIDs[STy])
        UnnamedStructIDs[STy] = NextTypeID++;
    return "l_unnamed_" + utostr(UnnamedStructIDs[STy]);
}

ClassMethodTable *getClass(const StructType *STy)
{
    int fieldSub = 0;
    if (!classCreate[STy]) {
        ClassMethodTable *table = new ClassMethodTable;
        classCreate[STy] = table;
        classCreate[STy]->STy = STy;
        ModuleIR *IR = new ModuleIR;
        table->IR = IR;
        IR->name = legacygetStructName(STy);
        if (startswith(IR->name, "l_module_OC_")) {
            IR->name = IR->name.substr(12);
printf("[%s:%d]CCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC %s\n", __FUNCTION__, __LINE__, IR->name.c_str());
        }
        int len = STy->structFieldMap.length();
        int subs = 0, last_subs = 0;
        int processSequence = 0; // fields
        if (STy->structFieldMap[0] == '!') { // isUnion
            subs++;
            last_subs++;
            while (subs < len) {
                while (subs < len && STy->structFieldMap[subs] != ',') {
                    subs++;
                }
                subs++;
                std::string ret = STy->structFieldMap.substr(last_subs);
                int idx = ret.find(',');
                if (idx >= 0)
                    ret = ret.substr(0,idx);
                idx = ret.find(':');
                std::string typName = ret.substr(idx+1);
                if (startswith(typName, "l_"))
                    typName = CBEMangle(typName);
                IR->unionList.push_back(UnionItem{ret.substr(0, idx), typName});
                last_subs = subs;
            }
        }
        else while (subs < len) {
            while (subs < len && STy->structFieldMap[subs] != ',') {
                subs++;
            }
            subs++;
            if (STy->structFieldMap[last_subs] == '/') {
                processSequence = 1; // methods
                last_subs++;
            }
            if (STy->structFieldMap[last_subs] == ';') {
                processSequence = 2; // software interfaces
                last_subs++;
            }
            if (STy->structFieldMap[last_subs] == '@') {
                processSequence = 3; // interface connect
                last_subs++;
            }
            std::string ret = STy->structFieldMap.substr(last_subs);
            int idx = ret.find(',');
            if (idx >= 0)
                ret = ret.substr(0,idx);
            idx = ret.find(':');
//printf("[%s:%d] sequence %d ret %s idx %d\n", __FUNCTION__, __LINE__, processSequence, ret.c_str(), idx);
            if (processSequence == 0) {
                std::string params;
                int lt = ret.find('<');
                if (lt >= 0) {
                    params = ret.substr(lt);
                    ret = ret.substr(0, lt);
                    idx = ret.find(':');
                }
                std::string options;
                std::string name = ret;
                if (idx >= 0) {
                    options = ret.substr(idx+1);
                    name = ret.substr(0, idx);
                }
                table->fieldName[fieldSub++] = FieldNameInfo{name, options, params};
            }
            else if (processSequence == 2)
                table->softwareName.push_back(ret);
            else if (processSequence == 3) { // interface connect
                std::string source = ret.substr(idx+1);
                std::string target = ret.substr(0, idx);
                std::string targetItem = target, targetInterface;
                idx = targetItem.find("$");
                if (idx > 0) {
                    targetInterface = targetItem.substr(idx+1);
                    targetItem = targetItem.substr(0, idx);
                }
                int Idx = 0;
printf("[%s:%d] CONNECT %s = %s target %s tif %s\n", __FUNCTION__, __LINE__, target.c_str(), source.c_str(), targetItem.c_str(), targetInterface.c_str());
                for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
                    Type *telement = *I;
                    if (const PointerType *PTy = dyn_cast<PointerType>(telement))
                        telement = PTy->getElementType();
                    if (const StructType *STyE = dyn_cast<StructType>(telement))
                    if (targetItem == fieldName(STy, Idx)) {
printf("[%s:%d] found targetitem %s\n", __FUNCTION__, __LINE__, targetItem.c_str());
                        int Idx = 0;
                        if (targetInterface == "") {
printf("[%s:%d] targetlocal\n", __FUNCTION__, __LINE__);
                            IR->interfaceConnect.push_back(InterfaceConnectType{target, source, getClass(STyE)->IR->name});
                            goto nextInterface;
                        }
                        else
                        for (auto I = STyE->element_begin(), E = STyE->element_end(); I != E; ++I, Idx++) {
printf("[%s:%d] targetif %s name %s\n", __FUNCTION__, __LINE__, targetInterface.c_str(), fieldName(STyE, Idx).c_str());
                            Type *element = *I;
                            if (const PointerType *PTy = dyn_cast<PointerType>(element))
                                element = PTy->getElementType();
                            if (const StructType *STyI = dyn_cast<StructType>(element))
                            if (targetInterface == fieldName(STyE, Idx)) {
printf("[%s:%d] FOUND sname %s\n", __FUNCTION__, __LINE__, STyI->getName().str().c_str());
                                IR->interfaceConnect.push_back(InterfaceConnectType{target, source, getClass(STyI)->IR->name});
                                goto nextInterface;
                            }
                        }
                    }
                }
        nextInterface:;
            }
            else if (idx >= 0) {
                if (Function *func = globalMod->getFunction(ret.substr(0, idx)))
                    pushWork(func, ret.substr(idx+1));
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

std::string GetValueName(const Value *Operand)
{
    const GlobalAlias *GA = dyn_cast<GlobalAlias>(Operand);
    const Value *V;
    if (GA && (V = GA->getAliasee()))
        Operand = V;
    if (const GlobalValue *GV = dyn_cast<GlobalValue>(Operand))
        return CBEMangle(GV->getName());
    std::string Name = Operand->getName();
    if (const Instruction *source = dyn_cast_or_null<Instruction>(Operand))
    if (source->getOpcode() == Instruction::Alloca)
        // Make the names unique across all methods in a class
        Name = globalMethodName + MODULE_SEPARATOR + Name;
    if (Name.empty()) { // Assign unique names to local temporaries.
        unsigned &No = AnonValueNumbers[Operand];
        if (No == 0)
            No = ++NextAnonValueNumber;
        Name = "tmp__" + utostr(No);
    }
    else if (Name != "this")
        if (auto arg = dyn_cast<Argument>(Operand)) {
            const Function *func = arg->getParent();
            for (auto item: getClass(findThisArgument(func))->method)
                if (item.second == func) {
                    Name = item.first.substr(0, item.first.length() - 5) + MODULE_SEPARATOR + Name;
                    goto allDone;
                }
            printf("[%s:%d] COULDNT FIND PARAMFUNC\n", __FUNCTION__, __LINE__);
            func->dump();
            exit(-1);
allDone:;
        }
    std::string VarName;
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
 * Calculate offset from base pointer for GEP
 */
static int64_t getGEPOffset(VectorType **LastIndexIsVector, gep_type_iterator I, gep_type_iterator E)
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
static int errorLimit = 5;
    VectorType *LastIndexIsVector = 0;
    int64_t Total = getGEPOffset(&LastIndexIsVector, I, E);
    ERRORIF(LastIndexIsVector);
    std::string cbuffer = printOperand(Ptr);
    bool removeSubscript = false;
    if (cbuffer == "_") { // optimization for verilog port names
        cbuffer = "";
    }
    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(Ptr))
    if (const ConstantDataArray *CPA = dyn_cast_or_null<ConstantDataArray>(globalVar->getInitializer())) {
        ERRORIF(!CPA->isString());
        cbuffer = printString(CPA->getAsString());
        removeSubscript = true;
    }
    if (trace_gep)
        printf("[%s:%d] cbuffer %s Total %ld\n", __FUNCTION__, __LINE__, cbuffer.c_str(), (unsigned long)Total);
    if (Total == -1) {
if (errorLimit > 0)
        printf("[%s:%d] non-constant offset cbuffer %s Total %ld\n", __FUNCTION__, __LINE__, cbuffer.c_str(), (unsigned long)Total);
    }
    if (I != E)
    if (const Constant *FirstOp = dyn_cast<Constant>(I.getOperand()))
    if (FirstOp->isNullValue() && std::next(I) != E)
        ++I;  // Skip the zero index if there are more items. (????)
    for (; I != E; ++I) {
        if (const StructType *STy = I.getStructTypeOrNull()) {
            uint64_t foffset = cast<ConstantInt>(I.getOperand())->getZExtValue();
            std::string fname = fieldName(STy, foffset);
            if (fname == "_")   // optimization for verilog port references
                fname = "";
            else if (cbuffer != "")  // optimization for verilog port references
                fname = MODULE_SEPARATOR + fname;
            if (trace_gep)
                printf("[%s:%d] cbuffer %s STy %s fname %s foffset %d\n", __FUNCTION__, __LINE__, cbuffer.c_str(), STy->getName().str().c_str(), fname.c_str(), (int) foffset);
            if (cbuffer == "this") {
                cbuffer = "";
                if (fname != "")
                    fname = fname.substr(1);
            }
            cbuffer += fname;
        }
        else {
            if (trace_gep)
                printf("[%s:%d] cbuffer %s\n", __FUNCTION__, __LINE__, cbuffer.c_str());
            std::string op = printOperand(I.getOperand());
            if (!removeSubscript || op != "0")
                cbuffer += "[" + op + "]";
        }
    }
    if (trace_gep || Total == -1)
if (Total != -1 || errorLimit-- > 0)
        printf("%s: return '%s'\n", __FUNCTION__, cbuffer.c_str());
    return cbuffer;
}

static ClassMethodTable *getFunctionTable(const Function *func)
{
    if (const StructType *targetSTy = findThisArgument(func))
        return getClass(targetSTy);
    return NULL;
}

std::string getMethodName(const Function *func)
{
    if (ClassMethodTable *targetTable = getFunctionTable(func))
        for (auto item: targetTable->method)
            if (item.second == func)
                return item.first;
    std::string fname = func->getName();
    if (fname == "printf")
        return "";
#if 0
    if (ClassMethodTable *targetTable = getFunctionTable(func))
        for (auto item: targetTable->method)
printf("[%s:%d] LOOKINGFOR %p itemfirst %s sec %p\n", __FUNCTION__, __LINE__, func, item.first.c_str(), item.second);
func->dump();
#endif
    return "";
}

const Function *getCallee(const Instruction *I)
{
    const CallInst *ICL = dyn_cast<CallInst>(I);
    const Value *val = ICL->getCalledValue();
    const Function *func = ICL->getCalledFunction();
    if (!func) {
        if (auto bcast = dyn_cast<ConstantExpr>(val))
            val = bcast->getOperand(0);
        func = dyn_cast<Function>(val);
    }
    return func;
}
/*
 * Generate a string for a function/method call
 */
static std::string printCall(const Instruction *I, bool useParams = false)
{
    const CallInst *ICL = dyn_cast<CallInst>(I);
    const Function *func = getCallee(I);
    std::string calledName = func->getName();
    std::string vout, sep, fname = getMethodName(func);
    CallSite CS(const_cast<Instruction *>(I));
    CallSite::arg_iterator AI = CS.arg_begin(), AE = CS.arg_end();
    if (!func) {
        printf("%s: not an instantiable call!!!! %s\n", __FUNCTION__, printOperand(*AI).c_str());
        I->dump();
        I->getParent()->getParent()->dump();
        parseError();
        exit(-1);
    }
    std::string pcalledFunction = printOperand(*AI++); // skips 'this' param
    if (trace_call || fname == "")
        printf("CALL: CALLER func %s[%p] pcalledFunction '%s' fname %s\n", calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
    if (calledName == "printf") {
        printf("CALL: PRINTFCALLER func %s[%p] pcalledFunction '%s' fname %s\n", calledName.c_str(), func, pcalledFunction.c_str(), fname.c_str());
        vout = "printf{" + pcalledFunction;
//.substr(1, pcalledFunction.length()-2);
        sep = ",";
        for (; AI != AE; ++AI) { // first param processed as pcalledFunction
            vout += sep + printOperand(*AI);
            sep = ",";
        }
        vout += "}";
    }
    else if (fname == "") {
        fname = "[ERROR_" + calledName + "_ERROR]";
        printf("[%s:%d] fname missing\n", __FUNCTION__, __LINE__);
        I->dump();
        exit(-1);
    }
    else {
        vout = pcalledFunction + MODULE_SEPARATOR + fname;
    if (useParams) {
        vout += "{";
        for (; AI != AE; ++AI) { // first param processed as pcalledFunction
            vout += sep + printOperand(*AI);
            sep = ",";
        }
        vout += "}";
    }
    }
    return vout;
}

std::string parenOperand(const Value *Operand)
{
    return "(" + printOperand(Operand) + ")";
}

static std::map<const BasicBlock *, std::list<BlockCondItem>> blockCondition;
static void setCondition(const BasicBlock *bb, bool invert, std::string val, const BasicBlock *from)
{
    // each element in list is a valid path to get to the target BasicBlock.
    // therefore the 'execute guard' for the BB is the 'OR' of all elements in the list.
    blockCondition[bb].push_back(BlockCondItem{invert, val, from});
}
static std::string getCondStr(const BasicBlock *bb)
{
    if (blockCondition[bb].size() == 1) {
        BlockCondItem &BC = blockCondition[bb].front();
        if (!blockCondition[BC.from].size()) {
            if (!BC.invert)
                return BC.cond;
            return "(" + BC.cond + " ^ 1)";
        }
    }
    std::string exprTop;
    for (auto item: blockCondition[bb]) {
        std::string thisTerm = item.cond;
        if (item.invert)
            // Since we are 'AND'ing conditions together, remove inversions
            thisTerm = "(" + thisTerm + "^ 1)";
        std::string condStr = getCondStr(item.from);
        if (condStr != "")
            // if BB where 'If' statement existed had a condition, 'AND' it in
            thisTerm = "(" + thisTerm + " & " + condStr + ")";
        if (exprTop != "")  // 'OR' together all paths of getting to this BB
            thisTerm = "(" + thisTerm + " | " + exprTop + ")";
        exprTop = thisTerm;
    }
    return exprTop;
}

static std::string typeName(const Type *Ty)
{
     switch (Ty->getTypeID()) {
     case Type::VoidTyID:
         return "";
     case Type::IntegerTyID:
         return "INTEGER_" + utostr(cast<IntegerType>(Ty)->getBitWidth());
     case Type::FloatTyID:
         return "FLOAT";
     case Type::StructTyID:
         return getClass(cast<StructType>(Ty))->IR->name;
     case Type::ArrayTyID: {
         const ArrayType *ATy = cast<ArrayType>(Ty);
         return "ARRAY_" + utostr(ATy->getNumElements()) + "_" + typeName(ATy->getElementType());
         }
     case Type::PointerTyID:
         return typeName(cast<PointerType>(Ty)->getElementType());
     default:
         printf("[%s:%d] unhandled ID %d\n", __FUNCTION__, __LINE__, Ty->getTypeID());
         Ty->dump();
         llvm_unreachable("Unhandled case in processTypes!");
     }
}
uint64_t sizeType(const Type *Ty)
{
    switch (Ty->getTypeID()) {
    case Type::VoidTyID:
        return 0;
    case Type::IntegerTyID:
        return cast<IntegerType>(Ty)->getBitWidth();
    case Type::FloatTyID:
         return sizeof(float) * 8; // HACKHACKHACK
    case Type::StructTyID: {
        uint64_t total = 0;
        const StructType *STy = cast<StructType>(Ty);
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I)
            total += sizeType(*I);
        return total;
        }
    case Type::ArrayTyID: {
        const ArrayType *ATy = cast<ArrayType>(Ty);
        return ATy->getNumElements() * sizeType(ATy->getElementType());
        }
    case Type::PointerTyID:
       return sizeType(cast<PointerType>(Ty)->getElementType());
    default:
        llvm_unreachable("Unhandled case in processTypes!");
    }
    printf("[%s:%d] sizeType FAILED\n", __FUNCTION__, __LINE__);
    Ty->dump();
    exit(-1);
}

/*
 * Generate a string for the value generated by an Instruction DAG
 */
std::string printOperand(const Value *Operand)
{
    static int depth;
    std::string cbuffer;
    if (!Operand)
        return "";
    depth++;
    if (const Instruction *I = dyn_cast<Instruction>(Operand)) {
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
            vout = printOperand(I->getOperand(0));
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
                vout += "-" + parenOperand(BinaryOperator::getNegArgument(cast<BinaryOperator>(I)));
            else if (BinaryOperator::isFNeg(I))
                vout += "-" + parenOperand(BinaryOperator::getFNegArgument(cast<BinaryOperator>(I)));
            else if (I->getOpcode() == Instruction::FRem) {
                if (I->getType() == Type::getFloatTy(I->getContext()))
                    vout += "fmodf(";
                else if (I->getType() == Type::getDoubleTy(I->getContext()))
                    vout += "fmod(";
                else  // all 3 flavors of long double
                    vout += "fmodl(";
                vout += printOperand(I->getOperand(0)) + ", "
                     + printOperand(I->getOperand(1)) + ")";
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
        case Instruction::Trunc: case Instruction::ZExt:
            //printf("printOperand: CASTTTTINNNNNNNNNNNNNNNN opcode %d.=%s\n", opcode, I->getOpcodeName());
            vout += printOperand(I->getOperand(0));
            break;
        case Instruction::BitCast: {
            StructType *inType = nullptr, *outType = nullptr;
            bool derived = checkDerived(I->getOperand(0)->getType(), I->getType());
            //printf("printOperand: BITCAASSSSS opcode %d.=%s derived %d\n", opcode, I->getOpcodeName(), derived);
            std::string operand = printOperand(I->getOperand(0));
            std::string replace, ctype;
            if (auto PTy = dyn_cast<PointerType>(I->getType()))
            if (auto STy = dyn_cast<StructType>(PTy->getElementType())) {
                outType = STy;
                ctype = typeName(outType);
                if (auto PTy = dyn_cast<PointerType>(I->getOperand(0)->getType()))
                if (auto STy = dyn_cast<StructType>(PTy->getElementType())) {
                    inType = STy;
                    ClassMethodTable *table = getClass(inType);
                    for (auto item: table->IR->unionList) {
                        printf("BBBBBBBB %s    UNION %s %s\n", ctype.c_str(), item.type.c_str(), item.name.c_str());
                        if (item.type == ctype) {
                            replace = MODULE_SEPARATOR + item.name;
                            break;
                        }
                    }
                }
            }
            if (derived || replace != "" || !inType || !outType)
                vout += operand + replace;
            else
                vout += "BITCAST_" + typeName(outType) + "(" + operand + ")";
            break;
            }

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
            for (unsigned opIndex = 0, Eop = PN->getNumIncomingValues(); opIndex < Eop; opIndex++) {
                BasicBlock *inBlock = PN->getIncomingBlock(opIndex);
                std::string cStr = getCondStr(inBlock);
                if (cStr != "")
                    vout += cStr + " ? ";
                vout += parenOperand(PN->getIncomingValue(opIndex));
                if (opIndex != Eop - 1)
                    vout += ":";
            }
            break;
            }
        case Instruction::Alloca:
            vout += GetValueName(I);
            break;
        default:
            printf("printOperand: Other opcode %d.=%s\n", opcode, I->getOpcodeName());
            I->getParent()->getParent()->dump();
            exit(1);
            break;
        }
        cbuffer += vout;
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
                //cbuffer += "(";
                int op = CE->getOpcode();
                assert (op == Instruction::GetElementPtr);
                // used for character string args to printf()
                cbuffer += printGEPExpression(CE->getOperand(0), gep_type_begin(CPV), gep_type_end(CPV));
// +  ")";
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
            else if (const ConstantFP *CFP = dyn_cast<ConstantFP>(CPV)) {
                SmallString<8> StrVal;
                CFP->getValueAPF().toString(StrVal);
                cbuffer += StrVal;
            }
            else {
                printf("[%s:%d] STRUCTUREDTYPES %p Operand %p\n", __FUNCTION__, __LINE__, I, Operand);
                Operand->dump();
                if (CPV) CPV->dump();
                ERRORIF(1); /* handle structured types */
            }
        }
    }
    if (trace_operand)
        printf("[%s:%d] depth %d return '%s'\n", __FUNCTION__, __LINE__, depth, cbuffer.c_str());
    depth--;
    return cbuffer;
}

static void processBlockConditions(const Function *currentFunction)
{
    for (auto BBI = currentFunction->begin(), BBE = currentFunction->end(); BBI != BBE; BBI++) {
        for (auto IIb = BBI->begin(), IE = BBI->end(); IIb != IE; IIb++) {
            const Instruction *II = &*IIb;
            switch (II->getOpcode()) {
            case Instruction::Br: {
                // BUG BUG BUG -> combine the condition for the current block with the getConditions for this instruction
                const BranchInst *BI = dyn_cast<BranchInst>(II);
                if (BI && BI->isConditional()) {
                    //printf("[%s:%d] condition %s [%p, %p]\n", __FUNCTION__, __LINE__, printOperand(BI->getCondition()).c_str(), BI->getSuccessor(0), BI->getSuccessor(1));
                    setCondition(BI->getSuccessor(0), false, parenOperand(BI->getCondition()), &*BBI); // 'true' condition
                    setCondition(BI->getSuccessor(1), true, parenOperand(BI->getCondition()), &*BBI); // 'inverted' condition
                }
                else if (isa<IndirectBrInst>(II)) {
                    printf("[%s:%d] indirect\n", __FUNCTION__, __LINE__);
                    for (unsigned i = 0, e = II->getNumOperands(); i != e; ++i) {
                        printf("[%d] = %s\n", i, printOperand(II->getOperand(i)).c_str());
                    }
                }
                else {
                    //printf("[%s:%d] BRUNCOND %p\n", __FUNCTION__, __LINE__, BI->getSuccessor(0));
                }
                break;
                }
            case Instruction::Switch: {
                const SwitchInst* SI = cast<SwitchInst>(II);
                //BasicBlock *defaultBB = SI->getDefaultDest();
                for (auto CI = SI->case_begin(), CE = SI->case_end(); CI != CE; ++CI) {
                    const BasicBlock *caseBB = CI->getCaseSuccessor();
                    int64_t val = CI->getCaseValue()->getZExtValue();
                    printf("[%s:%d] [%lld] = %s\n", __FUNCTION__, __LINE__, val, caseBB?caseBB->getName().str().c_str():"NONE");
                    if (getCondStr(caseBB) == "") // 'true' condition
                        setCondition(caseBB, false,
                             "(" + parenOperand(SI->getCondition()) + " == " + autostr(val) + ")", &*BBI);
                }
                break;
                }
            }
        }
    }
}

/*
 * Walk all BasicBlocks for a Function, generating strings for Instructions
 * that are not inlinable.
 */
static void processField(ClassMethodTable *table, FILE *OStr)
{
    // generate local state element declarations
    int Idx = 0;
    for (auto I = table->STy->element_begin(), E = table->STy->element_end(); I != E; ++I, Idx++) {
        auto fitem = getClass(table->STy)->fieldName[Idx];
        std::string fldName = fitem.name;
        const Type *element = *I;
        int64_t vecCount = -1;
        if (const Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = table->replaceCount[Idx];
        }
        if (fldName == "") {
            if (auto iSTy = dyn_cast<StructType>(element))
                processField(getClass(iSTy), OStr);
            continue;
        }
        if (const ArrayType *ATy = dyn_cast<ArrayType>(element)) {
            assert(vecCount == -1 && "both vecCount and array count are not allowed");
            vecCount = ATy->getNumElements();
            element = ATy->getElementType();
        }
        std::string temp;
        if (isa<PointerType>(element))
            temp += "/Ptr";
        if (fitem.options != "")
            temp += "/" + fitem.options;
        if (const PointerType *PTy = dyn_cast<PointerType>(element))
        if (const StructType *STy = dyn_cast<StructType>(PTy->getElementType()))
            element = STy;
        if (vecCount != -1)
            temp += "/Count " + utostr(vecCount) + " ";
        if (isInterface(dyn_cast<StructType>(element)))
            fprintf(OStr, "    INTERFACE%s %s %s\n", temp.c_str(), typeName(element).c_str(), fldName.c_str());
        else if (fldName != "__defaultClock" && fldName != "__defaultnReset")
            fprintf(OStr, "    FIELD%s %s %s\n", temp.c_str(), typeName(element).c_str(), fldName.c_str());
        if (fitem.params != "")
            fprintf(OStr, "    PARAMS %s %s\n", fldName.c_str(), fitem.params.c_str());
    }
}

std::string getRdyName(std::string basename)
{
    std::string rdyName = basename;
    if (endswith(rdyName, "__ENA"))
        rdyName = rdyName.substr(0, rdyName.length()-5);
    return rdyName + "__RDY";
}
static std::string processMethod(std::string methodName, const Function *func,
           std::list<std::string> &mlines, std::list<std::string> &malines)
{
    std::map<std::string, const Type *> allocaList;
    std::function<void(const Instruction *)> findAlloca = [&](const Instruction *II) -> void {
        if (II) {
        if (II->getOpcode() == Instruction::Alloca)
            allocaList[GetValueName(II)] = II->getType();
        else for (unsigned i = 0; i < II->getNumOperands(); i++)
            findAlloca(dyn_cast<Instruction>(II->getOperand(i)));
        }
    };
    globalMethodName = methodName;
    // Set up condition expressions for all BasicBlocks 
    processBlockConditions(func);
    NextAnonValueNumber = 0;
    /* Gather data for top level instructions in each basic block. */
    std::string retGuard, valsep;
    for (auto BI = func->begin(), BE = func->end(); BI != BE; ++BI) {
        std::string tempCond = getCondStr(&*BI);
        for (auto IIb = BI->begin(), IE = BI->end(); IIb != IE; IIb++) {
            const Instruction *II = &*IIb;
            switch(II->getOpcode()) {
            case Instruction::Store: {
                const StoreInst *SI = cast<StoreInst>(II);
                std::string value = printOperand(SI->getOperand(0));
                findAlloca(dyn_cast<Instruction>(SI->getPointerOperand()));
                std::string dest = printOperand(SI->getPointerOperand());
                std::string alloc = "STORE ";
                bool isInter = false;
                if (auto IG = dyn_cast<GetElementPtrInst>(SI->getPointerOperand()))
                    isInter = isInterface(dyn_cast<StructType>(IG->getSourceElementType()));
                if (isInter || dest == "__defaultClock" || dest == "__defaultnReset" || isAlloca(SI->getPointerOperand()))
                    alloc = "LET " + typeName(cast<PointerType>(
                      SI->getPointerOperand()->getType())->getElementType()) + " ";
                mlines.push_back(alloc + tempCond + ":" + dest + " = " + value);
                break;
                }
            case Instruction::Ret:
                if (!II->getNumOperands())
                    break;
                retGuard += valsep;
                if (tempCond != "")
                    retGuard += tempCond + " ? ";
                valsep = " : ";
                retGuard += parenOperand(II->getOperand(0));
                break;
            case Instruction::Call: { // can have value
                const Function *fcall = getCallee(II);
                if (fcall->getName() == "printf") {
                    mlines.push_back("PRINTF " + tempCond + ":" + printCall(II, true));
                    break;
                }
                std::string temp = (isActionMethod(fcall) ? "/Action " : " ") + tempCond;
                mlines.push_back("CALL" + temp + ":" + printCall(II, true));
                break;
                }
            }
        }
    }
    for (auto item: allocaList)
        malines.push_back("ALLOCA " + typeName(item.second) + " " + item.first);
    return retGuard;
}

static void processClass(ClassMethodTable *table, FILE *OStr)
{
    bool isModule = startswith(table->STy->getName(), "module");
    fprintf(OStr, "%sMODULE %s {\n", isModule ? "" : "E", table->IR->name.c_str());
    for (auto item: table->softwareName)
        fprintf(OStr, "    SOFTWARE %s\n", item.c_str());
    for (auto item: table->IR->priority)
        fprintf(OStr, "    PRIORITY %s %s\n", item.first.c_str(), item.second.c_str());
    for (auto item: table->IR->interfaceConnect)
        fprintf(OStr, "    INTERFACECONNECT %s %s %s\n", item.target.c_str(), item.source.c_str(), item.type.c_str());
    for (auto item: table->IR->unionList)
        fprintf(OStr, "    UNION %s %s\n", item.type.c_str(), item.name.c_str());
    if (table->IR->unionList.size())
        fprintf(OStr, "    FIELD INTEGER_%ld DATA\n", (long)sizeType(table->STy));
    else
        processField(table, OStr);
    for (auto FI : table->method) {
        std::list<std::string> mlines, malines;
        std::string methodName = FI.first;
        const Function *func = FI.second;
        std::string rdyName = getRdyName(methodName);
        std::string rdyGuard;
        if (endswith(methodName, "__RDY"))
            continue;
        if (trace_function || trace_call)
            printf("PROCESSING %s %s\n", func->getName().str().c_str(), methodName.c_str());
        if (isModule)
        if (auto rfunc = table->method[rdyName]) {
            std::list<std::string> mrlines;
            rdyGuard = processMethod(rdyName, rfunc, mrlines, mrlines);
            if (rdyGuard == "1")
                rdyGuard = "";
        }
        std::string retGuard = processMethod(methodName, func, mlines, malines);
        if (!isModule)
            retGuard = "";
        std::string headerLine = methodName;
        auto AI = func->arg_begin(), AE = func->arg_end();
        std::string sep = " ( ";
        for (AI++; AI != AE; ++AI) {
            headerLine += sep + typeName(AI->getType()) + " " + AI->getName().str();
            sep = " , ";
        }
        if (sep != " ( ")
            headerLine += " )";
        if (!isActionMethod(func))
            headerLine += " " + typeName(func->getReturnType());
        if (retGuard != "")
            headerLine += " = (" + retGuard + ")";
        if (rdyGuard != "")
            headerLine += " if (" + rdyGuard + ")";
        if (mlines.size() + malines.size())
            headerLine += " {";
        std::string options;
        if (table->ruleFunctions[globalMethodName])
            options += "/Rule";
        fprintf(OStr, "    METHOD%s %s\n", options.c_str(), headerLine.c_str());
        for (auto line: malines)
             fprintf(OStr, "        %s\n", line.c_str());
        for (auto line: mlines)
             fprintf(OStr, "        %s\n", line.c_str());
        if (mlines.size())
            fprintf(OStr, "    }\n");
    }
    fprintf(OStr, "}\n");
}

void generateIR(std::string OutputDir)
{
    std::map<std::string, const StructType *> structAlpha;
    for (auto current : classCreate) {
        assert(current.first);
        std::string sname = current.first->getName();
        std::string sortName =
              ( (!strncmp(sname.c_str(), "struct.", 7))      ? '1'
              : (!strncmp(sname.c_str(), "union.", 6))       ? '2'
              : (!strncmp(sname.c_str(), "class.", 6))       ? '4'
              : (!strncmp(sname.c_str(), "ainterface.", 11)) ? '5'
              : (!strncmp(sname.c_str(), "serialize.", 10))  ? '6'
              : (!strncmp(sname.c_str(), "emodule.", 8))     ? '7'
              : '9') + getClass(current.first)->IR->name;
        if (strncmp(sname.c_str(), "class.std::", 11) // don't generate anything for std classes
         && strncmp(sname.c_str(), "struct.std::", 12))
            structAlpha[sortName] = current.first;
    }
    FILE *OStrIR = fopen((OutputDir + ".generated.IR").c_str(), "w");
    for (auto item : structAlpha)
        processClass(getClass(item.second), OStrIR);
    fclose(OStrIR);
}
