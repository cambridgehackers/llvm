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

static std::map<const Function *, bool> actionFunction;
static std::map<const Function *, std::string> methodTemplateOptions;
static int trace_function;//=1;
static int trace_call;//=1;
static int trace_gep;//=1;
static int trace_operand;//=1;
static int trace_blockCond;//= 1;
static bool traceConnect;// = true;
static std::map<const StructType *,ClassMethodTable *> classCreate;
static unsigned NextTypeID;
static std::string globalMethodName;

static DenseMap<const Value*, unsigned> AnonValueNumbers;
static unsigned NextAnonValueNumber;
static DenseMap<const StructType*, unsigned> UnnamedStructIDs;
std::map<std::string, Function *> functionMap;
Module *globalMod;
static std::string processMethod(std::string methodName, const Function *func,
           std::list<std::string> &mlines, std::list<std::string> &malines, std::string localOptions);

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
    if (auto Icast = dyn_cast_or_null<Instruction>(arg)) {
        switch (Icast->getOpcode()) {
        case Instruction::SExt:
        case Instruction::FPTrunc: case Instruction::FPExt:
        case Instruction::FPToUI: case Instruction::FPToSI:
        case Instruction::UIToFP: case Instruction::SIToFP:
        case Instruction::IntToPtr: case Instruction::PtrToInt:
        case Instruction::AddrSpaceCast:
        case Instruction::Trunc: case Instruction::ZExt:
        case Instruction::Load:
            return isAlloca(Icast->getOperand(0));
        case Instruction::GetElementPtr:
            return isAlloca(cast<GetElementPtrInst>(arg)->getPointerOperand());
        case Instruction::Alloca:
            return true;
        case Instruction::Call: {
            const Function *func = cast<CallInst>(arg)->getCalledFunction();
            std::string calledName = func->getName();
            const Instruction *II = dyn_cast<Instruction>(arg);
            CallSite CS(const_cast<Instruction *>(II));
            CallSite::arg_iterator AI = CS.arg_begin();
            if ((calledName == "__bitsubstrl" || calledName == "__bitsubstr") && AI != CS.arg_end())
                return isAlloca(*AI);
            break;
            }
        }
    }
    if (const CastInst *IG = dyn_cast_or_null<CastInst>(arg))
        return isAlloca(IG->getOperand(0));
    if (auto AR = dyn_cast_or_null<Argument>(arg))
    if (AR->getName() != "this")
        return true;
    return false;
}

static bool isInterface(const Type *Ty)
{
    if (auto STy = dyn_cast<StructType>(Ty))
    if (!STy->isLiteral() && !STy->getName().empty())
        return startswith(STy->getName(), "ainterface.");
    if (auto ATy = dyn_cast<ArrayType>(Ty))
        return isInterface(ATy->getElementType());
    if (auto PTy = dyn_cast<PointerType>(Ty))
        return isInterface(PTy->getElementType());
    return false;
}

bool isActionMethod(const Function *func)
{
    return (func->getReturnType() == Type::getVoidTy(func->getContext()) || actionFunction[func]);
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
        std::string fname = table->fieldName[Idx].name;
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
        static const char *prefix[] = {"emodule.", "module.",
            "struct.",
            "ainterface.", "serialize.", "class.", "union.", nullptr};
        const char **p = prefix;
        while (*p) {
            if (startswith(temp, *p)) {
                temp = temp.substr(strlen(*p));
                if (temp.find(" ") != std::string::npos)
                    return CBEMangle(temp);
                int ind;
                while ((ind = temp.find(".")) != -1)
                    temp = temp.substr(0, ind) + "_OC_" + temp.substr(ind+1);
                return temp;
            }
            p++;
        }
printf("[%s:%d] NAME '%s'\n", __FUNCTION__, __LINE__, temp.c_str());
        exit(-1);
    }
    if (!UnnamedStructIDs[STy])
        UnnamedStructIDs[STy] = NextTypeID++;
    return "l_unnamed_" + utostr(UnnamedStructIDs[STy]);
}

static void buildInterfaceList(ClassMethodTable *master, ClassMethodTable *table, std::string prefix, bool top)
{
    int Idx = 0;
    for (auto I = table->STy->element_begin(), E = table->STy->element_end(); I != E; ++I, Idx++) {
        Type *telement = *I;
        if (auto PTy = dyn_cast<PointerType>(telement))
            telement = PTy->getElementType();
        if (auto ATy = dyn_cast<ArrayType>(telement))
            telement = ATy->getElementType();
        if (const StructType *STyE = dyn_cast<StructType>(telement)) {
            auto tableE = getClass(STyE);
            bool isInter = isInterface(STyE);
            std::string fname = prefix;
            if (traceConnect)
                printf("[%s:%d] [%d] top %d isifc %d prefix '%s' name '%s' type '%s'\n", __FUNCTION__, __LINE__, Idx, top, isInter, prefix.c_str(), table->fieldName[Idx].name.c_str(), tableE->name.c_str());
            if (prefix != "" && table->fieldName[Idx].name != "")
                fname += MODULE_SEPARATOR;
            fname += table->fieldName[Idx].name;
            if (isInter)
                master->interfaces[fname] = FieldNameInfo{tableE->name, "", "", "", ""};
            if (top || isInter)
                buildInterfaceList(master, tableE, fname, top && isInter);
        }
    }
}

static void classConnectInterface(ClassMethodTable *table, std::string target, std::string source, bool isForward)
{
    if (target.substr(0, 8) == "*(this->" && target.substr(target.length()-1) == ")")
        target = target.substr(8, target.length() - 9);
    if (traceConnect) {
        printf("[%s:%d] CONNECT %s = %s \n", __FUNCTION__, __LINE__, target.c_str(), source.c_str());
        for (auto item: table->interfaces)
            printf("[%s:%d]interfacetable [%s] = %s\n", __FUNCTION__, __LINE__, item.first.c_str(), item.second.name.c_str());
    }
    std::string sub, targetBase = target;
    int ind = targetBase.find("[");
    if (ind > 0) {
        sub = targetBase.substr(ind);
        targetBase = targetBase.substr(0, ind);
    }
    auto tifc = table->interfaces.find(targetBase);
    if (tifc != table->interfaces.end()) {
        std::string tname = tifc->second.name;
        //if (traceConnect)
            printf("[%s:%d] '%s' found '%s'\n", __FUNCTION__, __LINE__, target.c_str(), tname.c_str());
        table->interfaceConnect.push_back(GenInterfaceConnectType{target, source, tname, isForward});
    }
    else {
        printf("[%s:%d] Error: interface not found %s\n", __FUNCTION__, __LINE__, target.c_str());
        for (auto item: table->interfaces)
            printf("        Available: [%s] = %s\n", item.first.c_str(), item.second.name.c_str());
    }
}

std::map<std::string, const StructType *> structNameMap;
ClassMethodTable *getClass(const StructType *STy)
{
    int fieldSub = 0;
    if (!classCreate[STy]) {
        ClassMethodTable *table = new ClassMethodTable;
        classCreate[STy] = table;
        table->STy = STy;
        table->remapSTy = nullptr;
        table->name = legacygetStructName(STy);
        structNameMap[STy->getName().str()] = STy;
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
                table->unionList.push_back(GenUnionItem{ret.substr(0, idx), typName});
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
                buildInterfaceList(table, table, "", true);
                processSequence = 3; // interface connect
                last_subs++;
            }
            if (STy->structFieldMap[last_subs] == '%') {
                processSequence = 4; // structTy remap
                last_subs++;
            }
            std::string ret = STy->structFieldMap.substr(last_subs);
            int idx = ret.find(',');
            if (idx >= 0)
                ret = ret.substr(0,idx);
            idx = ret.find(':');
//printf("[%s:%d] sequence %d ret %s idx %d\n", __FUNCTION__, __LINE__, processSequence, ret.c_str(), idx);
            if (processSequence == 0) {
                std::string params, templateOptions, vecCount;
                int lt = ret.find('<');
                if (lt >= 0) {
                    params = ret.substr(lt);
                    ret = ret.substr(0, lt);
                    idx = ret.find(':');
                }
                lt = ret.find('#');
                if (lt >= 0) {
                    templateOptions = ret.substr(lt+1);
                    ret = ret.substr(0, lt);
                    idx = ret.find(':');
                }
                std::string options;
                std::string name = ret;
                if (idx >= 0) {
                    options = ret.substr(idx+1);
                    name = ret.substr(0, idx);
                }
                table->fieldName[fieldSub++] = FieldNameInfo{name, options, params, templateOptions, vecCount};
            }
            else if (processSequence == 2)
                table->softwareName.push_back(ret);
            else if (processSequence == 3) { // interface connect
                std::string source = ret.substr(idx+1);
                std::string target = ret.substr(0, idx);
                bool isForward = true;
                if (startswith(target, "CONNECT;")) {
                    isForward = false;
                    target = target.substr(8);
                }
                classConnectInterface(table, target, source, isForward);
            }
            else if (processSequence == 4) {
const StructType *newSTy = structNameMap[ret];
printf("[%s:%d] REMAPAPAPAPAPAPA %s new %p\n", __FUNCTION__, __LINE__, ret.c_str(), (void *)newSTy);
                table->remapSTy = newSTy;
            }
            else if (idx >= 0) { // processSequence == 1 -> methods
                std::string fname = ret.substr(0, idx);
                std::string mName = ret.substr(idx+1);
                std::string templateOptions, localOptions;
                int action = mName.find(":action");
                if (action > 0)
                    mName = mName.substr(0, action);
                int ind = mName.find("#");
                if (ind > 0) {
                    templateOptions = mName.substr(ind+1);
                    mName = mName.substr(0, ind);
                }
                if (Function *func = functionMap[fname]) {
                    methodTemplateOptions[func] = templateOptions;
                    pushWork(table, func, mName);
                    if (action > 0)
                        actionFunction[func] = true;
                }
                else
                    printf("[%s:%d]FFFFFFFFFFFFF table %s mname %s fname %s map %p\n", __FUNCTION__, __LINE__, table->name.c_str(), mName.c_str(), fname.c_str(), (void *)functionMap[fname]);
                }
            last_subs = subs;
        }
        checkClass(STy, STy);
    }
    auto table = classCreate[STy];
    if (table->remapSTy)
        return classCreate[table->remapSTy];
    return table;
}

/*
 * Name functions
 */

static std::string GetValueName(const Value *Operand)
{
    const GlobalAlias *GA = dyn_cast<GlobalAlias>(Operand);
    const Value *V;
    if (GA && (V = GA->getAliasee()))
        Operand = V;
    if (const GlobalValue *GV = dyn_cast<GlobalValue>(Operand))
        return CBEMangle(GV->getName());
    std::string Name = Operand->getName();
    if (const Instruction *source = dyn_cast_or_null<Instruction>(Operand))
    if (source->getOpcode() == Instruction::Alloca && globalMethodName != "")
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
            for (auto item: getClass(findThisArgument(func))->methods)
                if (!startswith(item.name, "FOR$"))
                if (item.func == func) { // prepend argument name with function name
                    Name = baseMethodName(item.name) + MODULE_SEPARATOR + Name;
                    break;
                }
        }
    if (endswith(Name, ".addr"))
        Name = Name.substr(0, Name.length() - 5);
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
static std::string printGEPExpression(const GetElementPtrInst *ref, const Value *Ptr, gep_type_iterator I, gep_type_iterator E)
{
static int errorLimit = 5;
static int nesting = 0;
    nesting++;
    VectorType *LastIndexIsVector = 0;
    int64_t Total = getGEPOffset(&LastIndexIsVector, I, E);
    ERRORIF(LastIndexIsVector);
    std::string cbuffer = printOperand(Ptr);
    bool processingInterface = false;
    if (auto IG = dyn_cast<GetElementPtrInst>(Ptr))
    if (auto PTy = dyn_cast<PointerType>(IG->getPointerOperand()->getType()))
        processingInterface = isInterface(PTy->getElementType());
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
    if (trace_gep) {
        printf("%s: START nest %d cbuffer %s Total %ld Ptr %p processingInterface %d\n", __FUNCTION__, nesting, cbuffer.c_str(), (unsigned long)Total, (void *)Ptr, processingInterface);
        Ptr->getType()->dump();
    }
    //if (Total == -1) {
//if (errorLimit > 0)
        //printf("[%s:%d] non-constant offset cbuffer %s Total %ld\n", __FUNCTION__, __LINE__, cbuffer.c_str(), (unsigned long)Total);
    //}
    if (I != E)
    if (const Constant *FirstOp = dyn_cast<Constant>(I.getOperand()))
    if (FirstOp->isNullValue() && std::next(I) != E)
        ++I;  // Skip the zero index if there are more items. (????)
int traceindex = 0;
    for (; I != E; ++I) {
        if (const StructType *STy = I.getStructTypeOrNull()) {
            uint64_t foffset = cast<ConstantInt>(I.getOperand())->getZExtValue();
            ClassMethodTable *table = getClass(STy);
            std::string fname = table->fieldName[foffset].name;
            if (fname == "_")   // optimization for verilog port references
                fname = MODULE_SEPARATOR;
            else if (cbuffer != "" && !processingInterface)  // optimization for verilog port references
                fname = MODULE_SEPARATOR + fname;
            if (trace_gep)
                printf("[%s:%d] nest %d cbuffer %s STy %s fname %s foffset %d, options %s\n", __FUNCTION__, __LINE__, nesting, cbuffer.c_str(), STy->getName().str().c_str(), fname.c_str(), (int) foffset, table->fieldName[foffset].options.c_str());
            if (cbuffer == "this") {
                cbuffer = "";
                if (fname != "" && fname.substr(0,1) == MODULE_SEPARATOR)
                    fname = fname.substr(1);
            }
printf("[%s:%d]DDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDD '%s' fname '%s'\n", __FUNCTION__, __LINE__, cbuffer.c_str(), fname.c_str());
            if (cbuffer[cbuffer.length()-1] == ']' && fname[0] == '$')
                fname = "." + fname.substr(1);                        // TODO: extend/regularize element selection
            cbuffer += fname;
            processingInterface = isInterface(STy);
        }
        else {
            if (trace_gep)
                printf("[%s:%d] nest %d cbuffer %s\n", __FUNCTION__, __LINE__, nesting, cbuffer.c_str());
            std::string op = printOperand(I.getOperand());
            if (!removeSubscript) {
                bool skip = false;
                int len = -1;
                if (auto ITy = dyn_cast<IntegerType>(I.getOperand()->getType()))
                    len = ITy->getBitWidth();
                skip = (traceindex == 0 && len == 32 && op == "0"); // skip over pointer
if (traceindex == 0 && len == 32) {
printf("[%s:%d] SUBBEEEZZZZZZZZZZZZZZZZZ index %d '%s' op %s len %d\n", __FUNCTION__, __LINE__, traceindex, cbuffer.c_str(), op.c_str(), len);
I.getOperand()->dump();
ref->dump();
}
                if (!skip)
                cbuffer += "[" + op + "]";
            }
            processingInterface = false;
        }
traceindex++;
    }
    if (trace_gep /*|| Total == -1*/)
if (Total != -1 || errorLimit-- > 0)
        printf("%s: END nest %d return '%s'\n", __FUNCTION__, nesting, cbuffer.c_str());
    nesting--;
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
        for (auto item: targetTable->methods)
            if (item.func == func)
                return item.name;
    std::string fname = func->getName();
    if (fname == "printf")
        return "";
#if 0
    if (ClassMethodTable *targetTable = getFunctionTable(func))
        for (auto item: targetTable->methods)
printf("[%s:%d] LOOKINGFOR %p itemfirst %s sec %p\n", __FUNCTION__, __LINE__, func, item.name.c_str(), item.func);
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
    const Function *func = getCallee(I);
    std::string calledName = func->getName();
    std::string vout, sep, fname = getMethodName(func);
    CallSite CS(const_cast<Instruction *>(I));
    CallSite::arg_iterator AI = CS.arg_begin(), AE = CS.arg_end();
    if (calledName == "__ValidReadyRuntime") {
        std::string val = printOperand(*AI);
        return val.substr(1, val.length() - 2);
    }
    if (calledName == "__bitsubstrl")
        calledName = "__bitsubstr";
    if (calledName == "__bitconcat" || calledName == "__bitsubstr" || calledName == "__reduce" || calledName == "__finish") {
        std::string val;
        for (; AI != AE; ++AI) {
            val += sep + printOperand(*AI);
            sep = ",";
        }
        return calledName + "{" + val + "}";
    }
    if (calledName == "llvm.clog2.i32") {
        return "__clog2{" + printOperand(*AI) + "}";
    }
    if (calledName == "$past") {
        return "$past{" + printOperand(*AI) + "}";
    }
    if (calledName == "__generateFor" || calledName == "__instantiateFor") {
        for (; AI != AE; ++AI) { // first param processed as pcalledFunction
            if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(*AI)) {
                int op = CE->getOpcode();
                Value *opd = CE->getOperand(0);
                if (op == Instruction::PtrToInt) {
                auto func = cast<Function>(opd);
                std::list<std::string> mlines, malines;
                std::string ret = processMethod("", func, mlines, malines, "");
                std::string methName = getMethodName(func);
                assert(methName != "");
                if (ret != "")
                    vout += "," + ret;
                else
                    vout += "," + methName;
                }
                else if (op == Instruction::GetElementPtr) {
                    // used for character string arg
                    std::string ret = printGEPExpression(dyn_cast<GetElementPtrInst>(CE), opd, gep_type_begin(CE), gep_type_end(CE));
                    vout += ret.substr(1, ret.length()-2); // remove leading/trailing '"'
                }
                else {
                    printf("[%s:%d]\n", __FUNCTION__, __LINE__);
                    CE->dump();
                    assert (op == Instruction::PtrToInt);
                }
            }
            else
                vout += "," + printOperand(*AI);
        }
        return vout;
    }
    if (!func) {
        printf("%s: not an instantiable call!!!! %s\n", __FUNCTION__, printOperand(*AI).c_str());
        I->dump();
        I->getParent()->getParent()->dump();
        parseError();
        exit(-1);
    }
    std::string pcalledFunction = printOperand(*AI++); // skips 'this' param
    if (trace_call || fname == "")
        printf("CALL: CALLER func %s[%p] pcalledFunction '%s' fname %s\n", calledName.c_str(), (void*)func, pcalledFunction.c_str(), fname.c_str());
    if (calledName == "printf") {
        printf("CALL: PRINTFCALLER func %s[%p] pcalledFunction '%s' fname %s\n", calledName.c_str(), (void*)func, pcalledFunction.c_str(), fname.c_str());
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
        if (pcalledFunction.substr(pcalledFunction.length() - 1) != MODULE_SEPARATOR)
            pcalledFunction += MODULE_SEPARATOR;
        vout = pcalledFunction + fname;
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
static std::map<const BasicBlock *, std::string> blockStr;
static std::map<const BasicBlock *, bool> getCondStrCheck;

static std::string getCondStr(const BasicBlock *bb, bool initCheck = false)
{
    if (initCheck)
        getCondStrCheck.clear();
    if (getCondStrCheck[bb]) {
        std::string name;
        if (bb->hasName())
            name = bb->getName();
        printf("%s: ERROR: loop in block cycle %s\n", __FUNCTION__, name.c_str());
        return "";
    }
    getCondStrCheck[bb] = true;
    auto bptr = blockStr.find(bb);
    if (bptr != blockStr.end())
        return bptr->second;
    std::string exprTop;
    if (blockCondition[bb].size() == 1) {
        BlockCondItem &BC = blockCondition[bb].front();
        if (!blockCondition[BC.from].size()) {
            if (!BC.invert)
                exprTop = BC.cond;
            else
                exprTop = "(" + BC.cond + " ^ 1)";
            goto retLabel;
        }
    }
    for (auto item: blockCondition[bb]) {
        std::string thisTerm = item.cond;
        if (item.invert)
            // Since we are 'AND'ing conditions together, remove inversions
            thisTerm = "(" + thisTerm + " ^ 1)";
        std::string condStr = getCondStr(item.from);
//printf("[%s:%d] %p bef term '%s' cond '%s' top %s\n", __FUNCTION__, __LINE__, bb, thisTerm.c_str(), condStr.c_str(), exprTop.c_str());
        if (condStr == "( 1 )")
            condStr = "";
        if (condStr != "") {
            if (thisTerm == "( 1 )")
                thisTerm = condStr;
            else
{
//printf("[%s:%d] %p conddddddddddddddddddand '%s' '%s'\n", __FUNCTION__, __LINE__, bb, thisTerm.c_str(), condStr.c_str());
                // if BB where 'If' statement existed had a condition, 'AND' it in
                thisTerm = "(" + thisTerm + " & " + condStr + ")";
}
        }
        if ("(" + thisTerm + " ^ 1)" == exprTop || "(" + exprTop + " ^ 1)" == thisTerm)
            thisTerm = "";
        else if (exprTop != "")  // 'OR' together all paths of getting to this BB
{
//printf("[%s:%d] %p conddddddddddddddddddor '%s' '%s'\n", __FUNCTION__, __LINE__, bb, thisTerm.c_str(), exprTop.c_str());
            thisTerm = "(" + thisTerm + " | " + exprTop + ")";
}
        exprTop = thisTerm;
    }
retLabel:
    if (exprTop == "( 1 )")
        exprTop = "";
    blockStr[bb] = exprTop;
    return exprTop;
}

static void processBlockConditions(const Function *currentFunction)
{
    blockCondition.clear();
    blockStr.clear();
    for (auto BBI = currentFunction->begin(), BBE = currentFunction->end(); BBI != BBE; BBI++) {
        auto setCondition = [&](const BasicBlock *bb, bool invert, std::string val, const BasicBlock *from) -> void {
            // each element in list is a valid path to get to the target BasicBlock.
            // therefore the 'execute guard' for the BB is the 'OR' of all elements in the list.
            blockCondition[bb].push_back(BlockCondItem{invert, val, &*BBI});
        };
        for (auto IIb = BBI->begin(), IE = BBI->end(); IIb != IE; IIb++) {
            const Instruction *II = &*IIb;
            switch (II->getOpcode()) {
            case Instruction::Br: {
                // BUG BUG BUG -> combine the condition for the current block with the getConditions for this instruction
                const BranchInst *BI = dyn_cast<BranchInst>(II);
                if (BI && BI->isConditional()) {
                    setCondition(BI->getSuccessor(0), false, parenOperand(BI->getCondition()), &*BBI); // 'true' condition
                    setCondition(BI->getSuccessor(1), true, parenOperand(BI->getCondition()), &*BBI); // 'inverted' condition
                }
                else if (isa<IndirectBrInst>(II)) {
                    printf("[%s:%d] indirect\n", __FUNCTION__, __LINE__);
                    for (unsigned i = 0, e = II->getNumOperands(); i != e; ++i) {
                        printf("[%d] = %s\n", i, printOperand(II->getOperand(i)).c_str());
                    }
                }
                else
                    setCondition(BI->getSuccessor(0), false, "( 1 )", &*BBI);
                break;
                }
            case Instruction::Switch: {
                const SwitchInst* SI = cast<SwitchInst>(II);
                std::string defaultCond, sep;
                for (auto CI = SI->case_begin(), CE = SI->case_end(); CI != CE; ++CI) {
                    const BasicBlock *caseBB = CI->getCaseSuccessor();
                    int64_t val = CI->getCaseValue()->getZExtValue();
                    printf("[%s:%d] [%d] = %s\n", __FUNCTION__, __LINE__, (int)val, caseBB?caseBB->getName().str().c_str():"NONE");
                    //if (getCondStr(caseBB, true) == "") { // 'true' condition
                        std::string sval = utostr(val);
                        std::string cond = parenOperand(SI->getCondition());
                        setCondition(caseBB, false, "(" + cond + " == " + sval + ")", &*BBI);
                        defaultCond += sep + "(" + cond + " == " + sval + ")";
                        sep = " | ";
                        //}
                }
                if (BasicBlock *defaultBB = SI->getDefaultDest())
                    setCondition(defaultBB, false, "((" + defaultCond + ") ^ 1)", &*BBI);
                break;
                }
            }
        }
    }
    if (trace_blockCond && blockCondition.size()) {
        printf("%s: blockconditions: %s\n", __FUNCTION__, currentFunction->getName().str().c_str());
        for (auto item: blockCondition) {
            printf("     block %s = %p\n", item.first->getName().str().c_str(), (void *)item.first);
            for (auto info: item.second) {
                printf("        invert %d cond %s from %p\n", info.invert, info.cond.c_str(), (void *)info.from);
            }
            printf("        condition: %s\n", getCondStr(item.first, true).c_str());
        }
    }
}

static std::string extractOptions(std::string ret, std::string &bitSize, std::string &arrayDim)
{
std::string orig = ret;
    int lt;
    std::string templateOptions;
    bitSize = ret;
    if ((lt = bitSize.find(':')) >= 0) {
        arrayDim = bitSize.substr(lt+1);
        bitSize = bitSize.substr(0, lt);
    }
    if ((lt = arrayDim.find(':')) >= 0) {
        templateOptions = arrayDim.substr(lt+1);
        arrayDim = arrayDim.substr(0, lt);
    }
    return templateOptions;
}

static std::string typeName(const Type *Ty, std::string templateOptions = "")
{
     std::string bitSize, arrayDim;
     std::string templOptions = extractOptions(templateOptions, bitSize, arrayDim);
//if (templateOptions != "")
//printf("[%s:%d]TEMPPEPEPE %s bit %s arr %s templ %s typeid %d\n", __FUNCTION__, __LINE__, templateOptions.c_str(), bitSize.c_str(), arrayDim.c_str(), templOptions.c_str(), Ty->getTypeID());
     switch (Ty->getTypeID()) {
     case Type::VoidTyID:
         return "";
     case Type::IntegerTyID:
         if (bitSize == "")
             bitSize = cast<IntegerType>(Ty)->getBitWidthString();
         return "Bit(" + bitSize + ")";
     case Type::FloatTyID:
         return "FLOAT";
     case Type::StructTyID: {
         std::string ret = getClass(cast<StructType>(Ty))->name;
         if (templOptions != "")
             printf("[%s:%d] classname %s template %s\n", __FUNCTION__, __LINE__, ret.c_str(), templOptions.c_str());
         return ret;
     }
     case Type::ArrayTyID: {
         const ArrayType *ATy = cast<ArrayType>(Ty);
         if (arrayDim == "")
             arrayDim = utostr(ATy->getNumElements());
         return "ARRAY_" + arrayDim + "_" + typeName(ATy->getElementType(), templateOptions);
         }
     case Type::PointerTyID:
         return typeName(cast<PointerType>(Ty)->getElementType(), templateOptions);
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
            vout = printGEPExpression(IG, IG->getPointerOperand(), gep_type_begin(IG), gep_type_end(IG));
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
            Type *outType = I->getType();
            bool derived = checkDerived(I->getOperand(0)->getType(), I->getType());
            //printf("printOperand: BITCAASSSSS opcode %d.=%s derived %d\n", opcode, I->getOpcodeName(), derived);
            std::string operand = printOperand(I->getOperand(0));
            std::string replace, ctype = typeName(outType);
            StructType *oSTy = nullptr;
            if (auto oPTy = dyn_cast<PointerType>(I->getOperand(0)->getType()))
                oSTy = dyn_cast<StructType>(oPTy->getElementType()); 
            if (!derived && oSTy) {
                ClassMethodTable *table = getClass(oSTy);
                for (auto item: table->unionList) {
                    printf("BBBBBBBB %s    UNION %s %s\n", ctype.c_str(), item.type.c_str(), item.name.c_str());
                    if (item.type == ctype) {
                        vout += operand + MODULE_SEPARATOR + item.name;
                        goto finish;
                    }
                }
            }
            //vout += "BITCAST_" + typeName(outType) + "(" + operand + ")";
            vout += operand;
finish:;
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
        case Instruction::Select: {
            vout += parenOperand(I->getOperand(0)) + " ? " + parenOperand(I->getOperand(1)) + " : " + parenOperand(I->getOperand(2));
            break;
        }
        case Instruction::PHI: {
            const PHINode *PN = dyn_cast<PHINode>(I);
            unsigned Eop = PN->getNumIncomingValues();
            {
            BasicBlock *startBlock = nullptr, *endBlock = nullptr;
            const Value *topVal = nullptr;
            bool hasFalse = false, hasTrue = false;
            for (unsigned opIndex = 0; opIndex < Eop; opIndex++) {
                BasicBlock *block = PN->getIncomingBlock(opIndex);
                const Value *operand = PN->getIncomingValue(opIndex);
                bool isBool = false;
                topVal = operand;
                endBlock = block;
                if (opIndex == Eop - 1)
                    break;
                const ConstantInt *CI = dyn_cast<ConstantInt>(operand);
                if (CI && CI->getType()->isIntegerTy(1)) {
                    isBool = true;
                    if (CI->getZExtValue())
                        hasTrue = true;
                    else
                        hasFalse = true;
                }
                else
                    goto legacy_phi;
                startBlock = block;
            }
            if (hasFalse == hasTrue)
                goto legacy_phi;
            std::string val;
            std::map<const BasicBlock *, int> termBlock;
            termBlock[PN->getParent()] = 1;
            /* now go through all blocks from start to last cond expr, building up expression */
            for (auto RI = Function::iterator(startBlock), RE = Function::iterator(endBlock); RI != RE; RI++) {
                auto TI = RI->getTerminator();
                const BranchInst *BI = dyn_cast_or_null<BranchInst>(TI);
                if (BI && BI->isConditional()) {
                    std::string bval = parenOperand(BI->getCondition());
                    const BasicBlock *tblock = BI->getSuccessor(0);
                    const BasicBlock *fblock = BI->getSuccessor(1);
                    const BasicBlock *nblock = &*std::next(RI);
                    bool isLAnd = tblock == nblock;
                    const BasicBlock *otherBlock = isLAnd ? fblock : tblock;
                    if (!termBlock[otherBlock]) {
                        termBlock[otherBlock] = 1;
                        val += "(";
                    }
                    val += bval;
                    if (termBlock[nblock])
                        val += ")";
                    val += (isLAnd ? " && " : " || ");
                }
                else {
                    goto legacy_phi;
                }
            }
            val += parenOperand(topVal);
            std::string cStr = getCondStr(startBlock, true);
            vout += val;
            break;
            }
legacy_phi:
            vout += "__phi(";
            std::string sep;
            for (unsigned opIndex = 0; opIndex < Eop; opIndex++) {
                BasicBlock *inBlock = PN->getIncomingBlock(opIndex);
                std::string cStr = getCondStr(inBlock, true);
                std::string val = parenOperand(PN->getIncomingValue(opIndex));
                if (cStr == "")
                    cStr = "__default";
                vout += sep + cStr + ":" + val;
                sep = ", ";
            }
            vout += ")";
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
        if (trace_operand)
             printf("[%s:%d] after depth %d op %s cbuffer %s vout %s\n", __FUNCTION__, __LINE__, depth, I->getOpcodeName(), cbuffer.c_str(), vout.c_str());
        cbuffer += vout;
    }
    else {
        //we need pointer to pass struct params (PipeIn)
        const Constant* CPV = dyn_cast<Constant>(Operand);
        if (trace_operand)
            printf("[%s:%d] before depth %d noninst %p CPV %p\n", __FUNCTION__, __LINE__, depth, (void *)Operand, (void *)CPV);
        if (!CPV || isa<GlobalValue>(CPV))
            cbuffer += GetValueName(Operand);
        else {
            /* handle expressions */
            ERRORIF(isa<UndefValue>(CPV) && CPV->getType()->isSingleValueType()); /* handle 'undefined' */
            if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(CPV)) {
                int op = CE->getOpcode();
                Value *opd = CE->getOperand(0);
                if (op == Instruction::PtrToInt) {
                    //used for printing guard exprs to 'instantiate for' items
                    const Function *func = dyn_cast<Function>(opd);
                    //cbuffer += func->getName().str();
                    std::list<std::string> mlines;
                    std::list<std::string> malines;
                    std::string ret = processMethod("", func, mlines, malines, "");
                    cbuffer += ret;
                }
                else if (op == Instruction::GetElementPtr) {
                    // used for character string args to printf()
                    cbuffer += printGEPExpression(dyn_cast<GetElementPtrInst>(CE), opd, gep_type_begin(CE), gep_type_end(CE));
                }
                else {
                    printf("[%s:%d] unknown Constant type\n", __FUNCTION__, __LINE__);
                    CE->dump();
                    assert (false);
                }
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
                printf("[%s:%d] STRUCTUREDTYPES %p Operand %p\n", __FUNCTION__, __LINE__, (void *)I, (void *)Operand);
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

/*
 * Walk all BasicBlocks for a Function, generating strings for Instructions
 * that are not inlinable.
 */
static void processField(ClassMethodTable *table, FILE *OStr, bool inInterface)
{
    // generate local state element declarations
    int Idx = 0;
    for (auto I = table->STy->element_begin(), E = table->STy->element_end(); I != E; ++I, Idx++) {
        auto fitem = table->fieldName[Idx];
        std::string fldName = fitem.name;
        //if (fldName == "_")
            //continue;
        std::string bitSize, arrayDim;
        std::string templateOptions = extractOptions(fitem.templateOptions, bitSize, arrayDim);
        const Type *element = *I;
        std::string vecCount;
        if (!inInterface)
        if (const Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = table->replaceCount[Idx];
        }
        if (fldName == "") {
            if (auto iSTy = dyn_cast<StructType>(element))
            if (!isInterface(iSTy))
                processField(getClass(iSTy), OStr, inInterface);
            continue;
        }
        std::string temp;
        if (const PointerType *PTy = dyn_cast<PointerType>(element)) {
            temp += "/Ptr";
            auto Ty = PTy->getElementType();
            if (const StructType *STy = dyn_cast<StructType>(Ty))
                element = Ty;
            else if (const ArrayType *STy = dyn_cast<ArrayType>(Ty))
                element = Ty;
        }
        if (const ArrayType *ATy = dyn_cast<ArrayType>(element)) {
            assert(vecCount == "" && "both vecCount and array count are not allowed");
            vecCount = utostr(ATy->getNumElements());
            element = ATy->getElementType();
        }
        if (vecCount != "" && arrayDim != "") {
printf("[%s:%d] vecCount %s array %s\n", __FUNCTION__, __LINE__, vecCount.c_str(), arrayDim.c_str());
            vecCount = arrayDim;
        }
        if (fitem.options != "")
            temp += "/" + fitem.options;
        if (vecCount != "")
            temp += "/Count " + vecCount + " ";
        std::string elementName = typeName(element);
        if (templateOptions != "") {
printf("[%s:%d] elementname %s templateopt %s\n", __FUNCTION__, __LINE__, elementName.c_str(), templateOptions.c_str());
            std::string name, remain = templateOptions;
            int ind = remain.find(":");
            if (ind > 0) {
                name = remain.substr(0, ind);
                remain = remain.substr(ind+1);
            }
            name += "(";
            if (!startswith(elementName, name)) {
                printf("[%s:%d] bad class name %s remain %s original %s\n", __FUNCTION__, __LINE__, elementName.c_str(), remain.c_str(), templateOptions.c_str());
                exit(-1);
            }
            std::string param = elementName.substr(name.length());
            param = param.substr(0, param.length()-1);
            while ((ind = param.find("=")) > 0) {
                name += param.substr(0, ind+1);
                param = param.substr(ind+1);
                ind = remain.find(":");
                std::string next;
                if (ind > 0) {
                    next = remain.substr(ind+1);
                    remain = remain.substr(0, ind);
                }
                name += remain;
                remain = next;
            }
            name += ")";
            //elementName = name;
printf("[%s:%d]NEWNAME was %s new %s\n", __FUNCTION__, __LINE__, elementName.c_str(), name.c_str());
        }
#define BOGUS_FORCE_DECLARATION_FIELD "$UNUSED$FIELD$FORCE$ALLOC$"
#define CONNECT_PREFIX "___CONNECT__"
        if (endswith(fldName, BOGUS_FORCE_DECLARATION_FIELD) || startswith(fldName, CONNECT_PREFIX))
            continue;
        if (isInterface(element))
            fprintf(OStr, "    INTERFACE%s %s %s\n", temp.c_str(), elementName.c_str(), fldName.c_str());
        else if (fldName != "__defaultClock" && fldName != "__defaultnReset")
            fprintf(OStr, "    FIELD%s %s %s\n", temp.c_str(), elementName.c_str(), fldName.c_str());
        if (fitem.params != "")
            fprintf(OStr, "    PARAMS %s %s\n", fldName.c_str(), fitem.params.c_str());
    }
}

std::string getRdyName(std::string basename)
{
    return baseMethodName(basename) + "__RDY";
}
std::string getInterfaceName(const Value *val)
{
    if (auto ins = dyn_cast<Instruction>(val)) {
        auto Ty = ins->getOperand(0)->getType();
        while (auto PTy = dyn_cast<PointerType>(Ty))
            Ty = PTy->getElementType();
        return legacygetStructName(dyn_cast<StructType>(Ty));
    }
    return "";
}
static std::string processMethod(std::string methodName, const Function *func,
           std::list<std::string> &mlines, std::list<std::string> &malines, std::string localOptions)
{
    std::map<std::string, const Type *> allocaList;
    std::string savedGlobalMethodName = globalMethodName;
    methodName = baseMethodName(methodName);
    globalMethodName = methodName;
    std::map<std::string, int> argumentName;
    std::map<std::string, std::string> localTemplate;
    int ind = localOptions.find("#");
    if (ind >= 0) {
        std::string tempBuf = localOptions.substr(ind+1);
        if (tempBuf[0] != ';') {
            printf("[%s:%d] ERROR Start %s tempBuf %s\n", __FUNCTION__, __LINE__, methodName.c_str(), tempBuf.c_str());
        }
        tempBuf = tempBuf.substr(1);
        while (tempBuf.length()) {
            ind = tempBuf.find(";");
            std::string name = tempBuf.substr(0, ind);
            std::string templ = tempBuf.substr(ind+1);
            tempBuf = "";
            ind = templ.find(";");
            if (ind >= 0) {
                tempBuf = templ.substr(ind+1);
                templ = templ.substr(0, ind);
            }
            localTemplate[methodName + MODULE_SEPARATOR + name] = templ;
        }
    }
    for (auto item = func->arg_begin(), eitem = func->arg_end(); item != eitem; item++) {
        std::string name = item->getName();
        if (name != "")
            argumentName[methodName + MODULE_SEPARATOR + name] = 1; // prepend argument name with function name
    }
    std::function<void(const Instruction *)> findAlloca = [&](const Instruction *II) -> void {
        if (II) {
        if (II->getOpcode() == Instruction::Alloca) {
            std::string name = GetValueName(II);
            if (!endswith(name, "$this") && name.find("$__inst$Genvar") == std::string::npos
             && !argumentName[name])
                allocaList[name] = II->getType();
        }
        else for (unsigned i = 0; i < II->getNumOperands(); i++)
            findAlloca(dyn_cast<Instruction>(II->getOperand(i)));
        }
    };
    // Set up condition expressions for all BasicBlocks 
    if (methodName != "") // don't need to clear/setup for __generateFor subcalls
                          // (destroys block condition setup for calling function)
        processBlockConditions(func);
    NextAnonValueNumber = 0;
    /* Gather data for top level instructions in each basic block. */
    std::string retGuard, valsep;
    for (auto BI = func->begin(), BE = func->end(); BI != BE; ++BI) {
        std::string tempCond = getCondStr(&*BI, true);
        bool thisPHI = false;
        for (auto IIb = BI->begin(), IE = BI->end(); IIb != IE; IIb++) {
            const Instruction *II = &*IIb;
            switch(II->getOpcode()) {
            case Instruction::Alloca:
                findAlloca(II);
                break;
            case Instruction::PHI:
                thisPHI = true;
                break;
            case Instruction::Store: {
                std::string localCond = thisPHI ? "" : tempCond;
                const StoreInst *SI = cast<StoreInst>(II);
                std::string value = printOperand(SI->getOperand(0));
                findAlloca(dyn_cast<Instruction>(SI->getOperand(0)));
                findAlloca(dyn_cast<Instruction>(SI->getPointerOperand()));
                std::string dest = printOperand(SI->getPointerOperand());
                std::string alloc = "STORE ";
                bool isInter = false;
                if (auto IG = dyn_cast<GetElementPtrInst>(SI->getPointerOperand()))
                    isInter = isInterface(IG->getType()) || isInterface(IG->getSourceElementType());
                if (isInter || dest == "__defaultClock" || dest == "__defaultnReset" || isAlloca(SI->getPointerOperand())) {
                    alloc = "LET " + typeName(cast<PointerType>(
                      SI->getPointerOperand()->getType())->getElementType()) + " ";
                    if (dest == value)  // when 'alloca' item matches parameter name
                        break;
                }
                mlines.push_back(alloc + localCond + ":" + dest + " = " + value);
                break;
                }
            case Instruction::Ret:
                if (!II->getNumOperands())
                    break;
                retGuard += valsep;
                if (tempCond != "")
                    retGuard += tempCond + " ? ";
                valsep = " : ";
                findAlloca(dyn_cast<Instruction>(II->getOperand(0)));
                retGuard += parenOperand(II->getOperand(0));
                break;
            case Instruction::Call: { // can have value
                const Function *fcall = getCallee(II);
                std::string calledName = fcall->getName();
                if (calledName == "__bitsubstrl")
                    calledName = "__bitsubstr";
                if (calledName == "__ValidReadyRuntime"
                 || calledName == "__bitconcat" || calledName == "__bitsubstr" || calledName == "__reduce")
                    break;                    // value picked up in expression
                if (calledName == "__generateFor") {
                    mlines.push_back("GENERATE " + tempCond + ":" + printCall(II, true));
                    break;
                }
                if (calledName == "__instantiateFor") {
                    mlines.push_back("INSTANTIATE " + tempCond + ":" + printCall(II, true));
                    break;
                }
                if (calledName == "printf") {
                    mlines.push_back("PRINTF " + tempCond + ":" + printCall(II, true));
                    break;
                }
                if (calledName == "__assert" || calledName == "__assume" || calledName == "__restrict") {
                    std::string val = printOperand(II->getOperand(0));
                    val = calledName.substr(2) + "(" + val.substr(1, val.length()-2) + ")";
                    mlines.push_back("ASSERT " + tempCond + ":" + val);
                    break;
                }
                if (calledName == "__connectInterface") {
                    const Function *F = II->getParent()->getParent();
                    auto *farg = F->arg_begin();
                    std::string target = printOperand(II->getOperand(0));
                    std::string source = printOperand(II->getOperand(1));
                    if (auto PT = dyn_cast<PointerType>(farg->getType()))
                    if (auto STy = dyn_cast<StructType>(PT->getElementType())) {
                        std::string type = getInterfaceName(II->getOperand(0));
                        if (type == "")
                            type = getInterfaceName(II->getOperand(1));
                        //classConnectInterface(getClass(STy), target, source, false);
                        bool isForward = false;
                        mlines.push_back("INTERFACECONNECT" +
                            std::string(isForward ? "/Forward" : "") + " " +
                            target + " " + source + " " + type);
                    }
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
        malines.push_back("ALLOCA " + typeName(item.second, localTemplate[item.first]) + " " + item.first);
    globalMethodName = savedGlobalMethodName; // make sure this is not destroyed by recursive calls (from __generateFor)
    return retGuard;
}

static void processClass(ClassMethodTable *table, FILE *OStr)
{
    std::string interfaceName;
    bool isModule = startswith(table->STy->getName(), "module");
    bool inInterface = isInterface(table->STy);
printf("[%s:%d]MODULE Ty %p %s -> %s\n", __FUNCTION__, __LINE__, (void *)table->STy, table->STy->getName().str().c_str(), table->name.c_str());
    const char *header = "MODULE";
    if (inInterface)
        header = "INTERFACE";
    else if (!isModule) {
        if (table->STy->getName().substr(0, 7) == "emodule")
            header = "EMODULE";
        else if (table->STy->getName().substr(0, 9) == "serialize")
            header = "SERIALIZE";
        else
            header = "STRUCT";
    }
#if 1
{
    // generate local state element declarations
    int Idx = 0;
    for (auto I = table->STy->element_begin(), E = table->STy->element_end(); I != E; ++I, Idx++) {
        auto fitem = table->fieldName[Idx];
        if (fitem.name != "")
            continue;
        std::string bitSize, arrayDim;
        std::string templateOptions = extractOptions(fitem.templateOptions, bitSize, arrayDim);
        const Type *element = *I;
        std::string vecCount;
        if (const ArrayType *ATy = dyn_cast<ArrayType>(element)) {
            assert(vecCount == "" && "both vecCount and array count are not allowed");
            vecCount = utostr(ATy->getNumElements());
            element = ATy->getElementType();
        }
        if (vecCount != "" && arrayDim != "") {
printf("[%s:%d] vecCount %s array %s\n", __FUNCTION__, __LINE__, vecCount.c_str(), arrayDim.c_str());
            vecCount = arrayDim;
        }
        std::string elementName = typeName(element);
        if (templateOptions != "") {
printf("[%s:%d] elementname %s templateopt %s\n", __FUNCTION__, __LINE__, elementName.c_str(), templateOptions.c_str());
            std::string name, remain = templateOptions;
            int ind = remain.find(":");
            if (ind > 0) {
                name = remain.substr(0, ind);
                remain = remain.substr(ind+1);
            }
            name += "(";
            if (!startswith(elementName, name)) {
                printf("[%s:%d] bad class name %s remain %s original %s\n", __FUNCTION__, __LINE__, elementName.c_str(), remain.c_str(), templateOptions.c_str());
                exit(-1);
            }
            std::string param = elementName.substr(name.length());
            param = param.substr(0, param.length()-1);
            while ((ind = param.find("=")) > 0) {
                name += param.substr(0, ind+1);
                param = param.substr(ind+1);
                ind = remain.find(":");
                std::string next;
                if (ind > 0) {
                    next = remain.substr(ind+1);
                    remain = remain.substr(0, ind);
                }
                name += remain;
                remain = next;
            }
            name += ")";
            //elementName = name;
printf("[%s:%d]NEWNAME was %s new %s\n", __FUNCTION__, __LINE__, elementName.c_str(), name.c_str());
        }
        if (isInterface(element))
            interfaceName = elementName;
    }
    if (!isInterface(table->STy))
    if (!table->STy->getName().startswith("struct."))
    if (interfaceName == "") {
printf("[%s:%d] interface name missing from module '%s'\n", __FUNCTION__, __LINE__, table->name.c_str());
table->STy->dump();
    }
}
#endif
    fprintf(OStr, "%s %s %s {\n", header, table->name.c_str(), interfaceName.c_str());
    for (auto item: table->softwareName)
        fprintf(OStr, "    SOFTWARE %s\n", item.c_str());
    for (auto item: table->priority)
        fprintf(OStr, "    PRIORITY %s %s\n", item.first.c_str(), item.second.c_str());
    for (auto item: table->interfaceConnect)
        fprintf(OStr, "    INTERFACECONNECT%s %s %s %s\n", item.isForward ? "/Forward" : "", item.target.c_str(), item.source.c_str(), item.type.c_str());
    for (auto item: table->unionList)
        fprintf(OStr, "    UNION %s %s\n", item.type.c_str(), item.name.c_str());
    if (table->unionList.size())
        fprintf(OStr, "    FIELD Bit(%ld) DATA\n", (long)sizeType(table->STy));
    else
        processField(table, OStr, inInterface);
    for (auto FI : table->methods) {
        std::list<std::string> mlines, malines;
        std::string methodName = FI.name;
        const Function *func = FI.func;
        if (!func) {
            printf("[%s:%d] name %s missing func %p\n", __FUNCTION__, __LINE__, methodName.c_str(), (void *)func);
            continue;
        }
        std::string rdyName = getRdyName(methodName);
        std::string rdyGuard;
        if (endswith(methodName, "__RDY"))
            continue;
        if (trace_function || trace_call)
            printf("PROCESSING %s %s\n", func->getName().str().c_str(), methodName.c_str());
        if (isModule)
        for(auto ritem: table->methods)
        if (ritem.name == rdyName) {
            std::list<std::string> mrlines;
            rdyGuard = processMethod(rdyName, ritem.func, mrlines, mrlines, methodTemplateOptions[ritem.func]);
            if (rdyGuard == "1")
                rdyGuard = "";
        }
        std::string retGuard = processMethod(methodName, func, mlines, malines, methodTemplateOptions[func]);
        if (!isModule)
            retGuard = "";
        std::string headerLine = methodName;
        auto AI = func->arg_begin(), AE = func->arg_end();
        std::string sep = " ( ";
        std::string returnOption = methodTemplateOptions[func];
        int ind = returnOption.find("#");
        if (ind >= 0) {
            //localOptions = returnOption.substr(ind+1);
            returnOption = returnOption.substr(0, ind);
        }
        std::string templateOptions;
        ind = returnOption.find(";");
        if (ind >= 0) {
            templateOptions = returnOption.substr(ind+1);
            returnOption = returnOption.substr(0, ind);
        }
        for (AI++; AI != AE; ++AI) {
            std::string thisOption = templateOptions;
            ind = thisOption.find(";");
            templateOptions = "";
            if (ind >= 0) {
                templateOptions = thisOption.substr(ind+1);
                thisOption = thisOption.substr(0, ind);
            }
            headerLine += sep + typeName(AI->getType(), thisOption) + " " + AI->getName().str();
            sep = " , ";
        }
        if (sep != " ( ")
            headerLine += " )";
        if (func->getReturnType() != Type::getVoidTy(func->getContext()))
            headerLine += " " + typeName(func->getReturnType(), returnOption);
        if (retGuard != "")
            headerLine += " = (" + retGuard + ")";
        if (rdyGuard != "")
            headerLine += " if (" + rdyGuard + ")";
        if (mlines.size() + malines.size())
            headerLine += " {";
        std::string options;
        if (table->ruleFunctions[globalMethodName])
            options += "/Rule";
        else if (startswith(methodName, "RULE")) //HACK for __rule declarations HACK HACK HACK
            options += "/Rule";                  //HACK for __rule declarations HACK HACK HACK
        if (isActionMethod(func))
            options += "/Action";
        fprintf(OStr, "    METHOD%s %s\n", options.c_str(), headerLine.c_str());
        for (auto line: malines)
             fprintf(OStr, "        %s\n", line.c_str());
        for (auto line: mlines)
             fprintf(OStr, "        %s\n", line.c_str());
        if (mlines.size() + malines.size())
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
              : '9') + getClass(current.first)->name;
        if (!current.second->remapSTy)
        if (strncmp(sname.c_str(), "class.std::", 11) // don't generate anything for std classes
         && strncmp(sname.c_str(), "struct.std::", 12))
            structAlpha[sortName] = current.first;
    }
    FILE *OStrIR = fopen((OutputDir + ".generated.IR").c_str(), "w");
    for (auto item : structAlpha)
        processClass(getClass(item.second), OStrIR);
    fclose(OStrIR);
}
