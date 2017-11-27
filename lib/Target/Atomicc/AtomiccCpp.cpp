//===-- AtomiccCpp.cpp - Generating Verilog from LLVM -----===//
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
#include "llvm/IR/Instructions.h"

using namespace llvm;

#include "AtomiccDecl.h"

/*
 * Generate element definitions for a class.
 */
static void generateClassElements(const StructType *STy, const StructType *ActSTy, FILE *OStr)
{
    std::string sname = getStructName(STy);
    ClassMethodTable *table = classCreate[STy];
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        std::string fname = fieldName(STy, Idx);
        Type *element = *I;
        int64_t vecCount = -1;
        if (table)
            if (Type *newType = table->replaceType[Idx]) {
                element = newType;
                vecCount = table->replaceCount[Idx];
            }
        if (fname == "unused_data_to_force_inheritance")
            continue;
        if (fname != "") {
            int dimIndex = 0;
            std::string vecDim;
            do {
                if (vecCount != -1)
                    vecDim = utostr(dimIndex++);
                std::string tname = fname + vecDim;
                std::string iname = tname;
                if (sname.substr(0,12) != "l_struct_OC_")
                if (!dyn_cast<StructType>(element) && !dyn_cast<PointerType>(element)) {
                    if (table)
                        table->shadow[tname] = 1;
                }
                if (!isInterface(dyn_cast<StructType>(element)))
                fprintf(OStr, "%s", printType(element, false, iname, "  ", ";\n", false).c_str());
            } while(vecCount-- > 0);
        }
        else if (const StructType *inherit = dyn_cast<StructType>(element))
            generateClassElements(inherit, ActSTy, OStr);
    }
}

/*
 * Generate string for class method declaration
 */
static std::string printFunctionSignature(const Function *F, std::string altname, bool addThis)
{
    std::string sep, statstr, tstr = altname + '(';
    FunctionType *FT = cast<FunctionType>(F->getFunctionType());
    ERRORIF (F->hasDLLImportStorageClass() || F->hasDLLExportStorageClass() || FT->isVarArg());
    Type *retType = F->getReturnType();
    auto AI = F->arg_begin(), AE = F->arg_end();
    if (F->hasLocalLinkage()) statstr = "static ";
    ERRORIF(F->isDeclaration());
    if (addThis) {
        tstr += "void *thisarg";
        sep = ", ";
    }
    AI++;
    for (; AI != AE; ++AI) {
        Type *element = AI->getType();
        if (auto PTy = dyn_cast<PointerType>(element))
            element = PTy->getElementType();
        tstr += printType(element, /*isSigned=*/false, GetValueName(AI), sep, "", false);
        sep = ", ";
    }
    if (sep == "")
        tstr += "void";
    return printType(retType, /*isSigned=*/false, tstr + ')', statstr, "", false);
}
static std::string printFunctionInstance(const Function *F, std::string altname, std::string firstArg)
{
    FunctionType *FT = cast<FunctionType>(F->getFunctionType());
    ERRORIF (F->hasDLLImportStorageClass() || F->hasDLLExportStorageClass() || FT->isVarArg());
    ERRORIF(F->isDeclaration());
    auto AI = F->arg_begin(), AE = F->arg_end();
    std::string tstr;
    AI++;
    if (F->getReturnType() != Type::getVoidTy(F->getContext()))
        tstr += "return ";
    tstr += altname + "(" + firstArg;
    for (; AI != AE; ++AI)
        tstr += ", " + GetValueName(AI);
    return tstr + ')';
}

/*
 * Generate class definition into output file.  Class methods are
 * only generated as prototypes.
 */
void generateClassDef(const StructType *STy, FILE *OStr, FILE *OHdr)
{
    ClassMethodTable *table = classCreate[STy];
    std::string name = getStructName(STy);
    std::map<std::string, int> cancelList;
    bool inInterface = isInterface(STy);
    bool inTypedef = name.substr(0,12) == "l_struct_OC_";

    // first generate '.h' file
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        Type *element = *I;
        int64_t vecCount = -1;
        if (table)
        if (Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = table->replaceCount[Idx];
        }
        std::string fname = fieldName(STy, Idx);
        if (const StructType *iSTy = dyn_cast<StructType>(element)) {
            std::string sname = getStructName(iSTy);
            if (!isInterface(iSTy)) {
            int dimIndex = 0;
            std::string vecDim;
            if (fname != "" && sname.substr(0,12) != "l_struct_OC_")
            do {
                if (vecCount != -1)
                    vecDim = utostr(dimIndex++);
            } while(vecCount-- > 0);
            }
        }
    }
    if (inTypedef)
        fprintf(OHdr, "typedef struct {\n");
    else {
        if (!inInterface) {
        fprintf(OHdr, "class %s;\n", name.c_str());
        for (auto FI : table->method) {
            Function *func = FI.second;
            if (!func)
                continue;
            std::string mname = FI.first;
            fprintf(OHdr, "extern %s;\n", printFunctionSignature(func, name + "__" + mname, true).c_str());
        }
        }
        fprintf(OHdr, "class %s {\npublic:\n", name.c_str());
    }
    generateClassElements(STy, STy, OHdr);
    //for (auto item: table->interfaceConnect)
        //fprintf(OHdr, "    %s = &%s;\n", item.target.c_str(), item.source.c_str());
    for (auto FI : table->method) {
        Function *func = FI.second;
        if (!func)
            continue;
        std::string mname = FI.first;
        if (!cancelList[mname])
        fprintf(OHdr, "  %s { %s; }\n", printFunctionSignature(func, mname, false).c_str(),
            printFunctionInstance(func, name + "__" + mname, "this").c_str());
    }
    fprintf(OHdr, "}%s;\n", inTypedef ? name.c_str() : "");
    if (inTypedef || inInterface)
        return;

    // now generate '.cpp' file
    for (auto FI : table->method) {
        Function *func = FI.second;
        if (!func)
            continue;
        std::string mname = FI.first;
printf("[%s:%d] generate %s\n", __FUNCTION__, __LINE__, mname.c_str());
func->dump();
        fprintf(OStr, "%s {\n", printFunctionSignature(func, name + "__" + mname, true).c_str());
        auto AI = func->arg_begin();
        std::string argt = printType(AI->getType(), /*isSigned=*/false, "", "", "", false);
        fprintf(OStr, "        %s thisp = (%s)thisarg;\n", argt.c_str(), argt.c_str());
        for (auto info: declareList[func])
            if (auto *PTy = dyn_cast<PointerType>(info->getType()))
                fprintf(OStr, "        %s;\n", printType(PTy->getElementType(), false, GetValueName(info), "", "", false).c_str());
        for (auto info: storeList[func]) {
            std::string pdest = printOperand(info->getPointerOperand(), true);
            if (pdest[0] == '&')
                pdest = pdest.substr(1);
            Value *cond = getCondition(info->getParent(), 0);
            std::string items = printOperand(info->getOperand(0), false);
            if (cond)
                fprintf(OStr, "        if (%s) {\n    ", printOperand(cond, false).c_str());
            fprintf(OStr, "        %s = %s;\n", pdest.c_str(), items.c_str());
            if (cond)
                fprintf(OStr, "        }\n    ");
        }
        for (auto info: functionList[func]) {
            if (Value *cond = getCondition(info->getParent(), 0))
                fprintf(OStr, "        if (%s)\n    ", printOperand(cond, false).c_str());
            fprintf(OStr, "        return %s;\n", printOperand(info->getOperand(0), false).c_str());
        }
        for (auto info: callList[func]) {
            if (Value *cond = getCondition(info->getParent(), 0))
                fprintf(OStr, "        if (%s)\n    ", printOperand(cond, false).c_str());
            fprintf(OStr, "        %s;\n", printCall(info).c_str());
        }
        fprintf(OStr, "}\n");
    }
}
