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

std::string baseMethod(std::string mname)
{
    if (endswith(mname, "__ENA"))
        return mname.substr(0, mname.length() - 5);
    else if (endswith(mname, "__VALID"))
        return mname.substr(0, mname.length() - 7);
    return mname;
}
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
                std::string delimStr = ";\n";
                if (sname.substr(0,12) != "l_struct_OC_")
                if (!dyn_cast<StructType>(element) && !dyn_cast<PointerType>(element)) {
                    if (table)
                        table->shadow[tname] = 1;
                    iname += ", " + tname + "_shadow";
                    delimStr = "; bool " + tname + "_valid;\n";
                }
                fprintf(OStr, "%s", printType(element, false, iname, "  ", delimStr, false).c_str());
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
    std::list<std::string> runLines;
    ClassMethodTable *table = classCreate[STy];
    std::string name = getStructName(STy);
    std::map<std::string, int> cancelList;
    bool inInterface = inheritsModule(STy, "class.InterfaceClass");
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
            if (!inheritsModule(iSTy, "class.InterfaceClass")) {
            int dimIndex = 0;
            std::string vecDim;
            if (fname != "" && sname.substr(0,12) != "l_struct_OC_")
            do {
                if (vecCount != -1)
                    vecDim = utostr(dimIndex++);
                runLines.push_back(fname + vecDim);
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
            std::string mname = baseMethod(pushSeen[func]);
            fprintf(OHdr, "extern %s;\n", printFunctionSignature(func, name + "__" + mname, true).c_str());
        }
        }
        fprintf(OHdr, "class %s {\npublic:\n", name.c_str());
    }
    generateClassElements(STy, STy, OHdr);
    if (inInterface) {
        fprintf(OHdr, "public:\n");
        for (auto FI : table->method) {
            Function *func = FI.second;
            std::string mname = baseMethod(pushSeen[func]);
            fprintf(OHdr, "  %s { %s; }\n", printFunctionSignature(func, mname, false).c_str(),
                printFunctionInstance(func, mname + "p", "p").c_str());
        }
        std::string delim;
        fprintf(OHdr, "  %s(", name.c_str());
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            std::string fname = fieldName(STy, Idx);
            if (fname != "") {
               fprintf(OHdr, "%sdecltype(%s) a%s", delim.c_str(), fname.c_str(), fname.c_str());
               delim = ", ";
            }
        }
        fprintf(OHdr, ") {\n");
        Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            std::string fname = fieldName(STy, Idx);
            if (fname != "")
               fprintf(OHdr, "    %s = a%s;\n", fname.c_str(), fname.c_str());
        }
        fprintf(OHdr, "  }\n");
    }
    else if (!inTypedef) {
        fprintf(OHdr, "public:\n  void run();\n  void commit();\n");
    if (table->interfaceList.size() > 0 || table->interfaceConnect.size() > 0) {
        std::string prefix = ":";
        fprintf(OHdr, "  %s()", name.c_str());
        for (auto item: table->interfaceList) {
            fprintf(OHdr, "%s\n      %s(this", prefix.c_str(), item.name.c_str());
            ClassMethodTable *itable = classCreate[item.STy];
            for (auto iitem: itable->method) {
                Function *func = iitem.second;
                std::string vname = item.name + '$' + iitem.first;
                // HACKHACKHACK: we don't know that the names match!!!!
                cancelList[vname] = 1;
                if (Function *rdyFunc = ruleRDYFunction[func]) {
                    std::string fname = name + "__" + vname;
                    std::string rname = name + "__" + item.name + '$' + pushSeen[rdyFunc];
                    fprintf(OHdr, ", %s, %s", rname.c_str(), fname.c_str());
                    prefix = ",";
                }
            }
            fprintf(OHdr, ")");
        }
        fprintf(OHdr, " {\n");
        for (auto item: table->interfaceConnect)
            fprintf(OHdr, "    %s = &%s;\n", item.target.c_str(), item.source.c_str());
        fprintf(OHdr, "  }\n");
    }
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string mname = baseMethod(pushSeen[func]);
        if (!cancelList[mname])
        fprintf(OHdr, "  %s { %s; }\n", printFunctionSignature(func, mname, false).c_str(),
            printFunctionInstance(func, name + "__" + mname, "this").c_str());
    }
    for (auto item: table->interfaces)
        fprintf(OHdr, "  void set%s(%s) { %s = v; }\n", item.first.c_str(),
            printType(item.second, false, "v", "", "", false).c_str(), item.first.c_str());
    }
    fprintf(OHdr, "}%s;\n", inTypedef ? name.c_str() : "");
    if (inTypedef || inInterface)
        return;

    // now generate '.cpp' file
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string mname = baseMethod(pushSeen[func]);
        fprintf(OStr, "%s {\n", printFunctionSignature(func, name + "__" + mname, true).c_str());
        auto AI = func->arg_begin();
        std::string argt = printType(AI->getType(), /*isSigned=*/false, "", "", "", false);
        fprintf(OStr, "        %s thisp = (%s)thisarg;\n", argt.c_str(), argt.c_str());
        for (auto info: table->declareList[func])
            if (auto *PTy = dyn_cast<PointerType>(info->getType()))
                fprintf(OStr, "        %s;\n", printType(PTy->getElementType(), false, GetValueName(info), "", "", false).c_str());
        for (auto info: table->storeList[func]) {
            std::string pdest = printOperand(info->getPointerOperand(), true);
            if (pdest[0] == '&')
                pdest = pdest.substr(1);
            appendList(MetaWrite, info->getParent(), pdest);
            Value *cond = getCondition(info->getParent(), 0);
            std::string items = printOperand(info->getOperand(0), false);
            if (cond)
                fprintf(OStr, "        if (%s) {\n    ", printOperand(cond, false).c_str());
            if (pdest.substr(0, 7) == "thisp->" && table->shadow[pdest.substr(7)]) {
                // State element updates are written to shadow variables so that changes
                // in state are not visible until 'commit()' method is called.
                fprintf(OStr, "        %s_shadow = %s;\n", pdest.c_str(), items.c_str());
                fprintf(OStr, "        %s_valid = 1;\n", pdest.c_str());
            }
            else
                fprintf(OStr, "        %s = %s;\n", pdest.c_str(), items.c_str());
            if (cond)
                fprintf(OStr, "        }\n    ");
        }
        for (auto info: table->functionList[func]) {
            if (Value *cond = getCondition(info->getParent(), 0))
                fprintf(OStr, "        if (%s)\n    ", printOperand(cond, false).c_str());
            fprintf(OStr, "        return %s;\n", printOperand(info->getOperand(0), false).c_str());
        }
        for (auto info: table->callList[func]) {
            if (Value *cond = getCondition(info->getParent(), 0))
                fprintf(OStr, "        if (%s)\n    ", printOperand(cond, false).c_str());
            fprintf(OStr, "        %s;\n", printCall(*info).c_str());
        }
        fprintf(OStr, "}\n");
    }
    // Generate 'run()' method to execute all rules in this and contained Modules
    fprintf(OStr, "void %s::run()\n{\n", name.c_str());
    for (auto item : table->ruleFunctions)
        if (item.second)
            fprintf(OStr, "    if (%s__RDY()) %s();\n", item.first.c_str(), item.first.c_str());
    for (auto item : runLines)
        fprintf(OStr, "    %s.run();\n", item.c_str());
    fprintf(OStr, "    commit();\n}\n");
    // Generate 'commit()' method to copy values from shadow variable into state elements
    fprintf(OStr, "void %s::commit()\n{\n", name.c_str());
    Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        Type *element = *I;
        int64_t vecCount = -1;
        if (table)
        if (Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = table->replaceCount[Idx];
        }
        std::string fname = fieldName(STy, Idx);
        if (fname != "" && !dyn_cast<StructType>(element) && !dyn_cast<PointerType>(element)) {
            fprintf(OStr, "    if (%s_valid) %s = %s_shadow;\n", fname.c_str(), fname.c_str(), fname.c_str());
            fprintf(OStr, "    %s_valid = 0;\n", fname.c_str());
        }
    }
    for (auto item : runLines)
        fprintf(OStr, "    %s.commit();\n", item.c_str());
    fprintf(OStr, "}\n");
}
