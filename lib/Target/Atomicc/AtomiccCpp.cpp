/* Copyright (c) 2015 The Connectal Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
// Portions of this program were derived from source with the license:
//     This file is distributed under the University of Illinois Open Source
//     License. See LICENSE.TXT for details.
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
 * Recursively generate element definitions for a class.
 */
static void generateClassElements(const StructType *STy, const StructType *ActSTy, FILE *OStr)
{
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
static void addIncludeName(StringMapType &includeList, const StructType *iSTy)
{
     std::string sname = getStructName(iSTy);
     if (!inheritsModule(iSTy, "class.BitsClass")
       && sname != "l_class_OC_InterfaceClass"
       && sname != "l_class_OC_Module")
         includeList[sname] = 1;
}
void generateClassDef(const StructType *STy, std::string oDir)
{
    std::list<std::string> runLines;
    StringMapType includeList;
    ClassMethodTable *table = classCreate[STy];
    std::string name = getStructName(STy);
    std::map<std::string, int> cancelList;
    bool inInterface = inheritsModule(STy, "class.InterfaceClass");

    // first generate '.h' file
    FILE *OStr = fopen((oDir + "/" + name + ".h").c_str(), "w");
    fprintf(OStr, "#ifndef __%s_H__\n#define __%s_H__\n", name.c_str(), name.c_str());
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
            if (const StructType *iSTy = dyn_cast<StructType>(element))
                if (!inheritsModule(iSTy, "class.BitsClass")) {
                    std::string sname = getStructName(iSTy);
                    addIncludeName(includeList, iSTy);
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
            if (const PointerType *PTy = dyn_cast<PointerType>(element))
            if (const StructType *iSTy = dyn_cast<StructType>(PTy->getElementType()))
                addIncludeName(includeList, iSTy);
    }
    for (auto FI : table->method) {
        Function *func = FI.second;
        Type *retType = func->getReturnType();
        auto AI = func->arg_begin(), AE = func->arg_end();
        if (const StructType *iSTy = dyn_cast<StructType>(retType))
            addIncludeName(includeList, iSTy);
        AI++;
        for (; AI != AE; ++AI) {
            Type *element = AI->getType();
            if (auto PTy = dyn_cast<PointerType>(element))
                element = PTy->getElementType();
            if (const StructType *iSTy = dyn_cast<StructType>(element))
                addIncludeName(includeList, iSTy);
        }
    }
    for (auto item: includeList)
        fprintf(OStr, "#include \"%s.h\"\n", item.first.c_str());
    if (name.substr(0,12) == "l_struct_OC_")
        fprintf(OStr, "typedef struct {\n");
    else {
        if (!inInterface) {
        fprintf(OStr, "class %s;\n", name.c_str());
        for (auto FI : table->method) {
            Function *func = FI.second;
            std::string mname = FI.first;
            fprintf(OStr, "extern %s;\n", printFunctionSignature(func, name + "__" + mname, true).c_str());
        }
        }
        fprintf(OStr, "class %s {\n", name.c_str());
    }
    fprintf(OStr, "public:\n");
    generateClassElements(STy, STy, OStr);
    if (inInterface) {
        fprintf(OStr, "public:\n");
        for (auto FI : table->method) {
            Function *func = FI.second;
            std::string mname = FI.first;
            fprintf(OStr, "  %s { %s; }\n", printFunctionSignature(func, mname, false).c_str(),
                printFunctionInstance(func, mname + "p", "p").c_str());
        }
        std::string delim;
        fprintf(OStr, "  %s(", name.c_str());
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            std::string fname = fieldName(STy, Idx);
            if (fname != "") {
               fprintf(OStr, "%sdecltype(%s) a%s", delim.c_str(), fname.c_str(), fname.c_str());
               delim = ", ";
            }
        }
        fprintf(OStr, ") {\n");
        Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            std::string fname = fieldName(STy, Idx);
            if (fname != "")
               fprintf(OStr, "    %s = a%s;\n", fname.c_str(), fname.c_str());
        }
        fprintf(OStr, "  }\n");
    }
    else if (name.substr(0,12) != "l_struct_OC_") {
        fprintf(OStr, "public:\n  void run();\n  void commit();\n");
    if (table->interfaceList.size() > 0 || table->interfaceConnect.size() > 0) {
        std::string prefix = ":";
        fprintf(OStr, "  %s()", name.c_str());
        for (auto item: table->interfaceList) {
            fprintf(OStr, "%s\n      %s(this", prefix.c_str(), item.name.c_str());
            ClassMethodTable *itable = classCreate[item.STy];
            for (auto iitem: itable->method) {
                Function *func = iitem.second;
                std::string vname = iitem.first;
                // HACKHACKHACK: we don't know that the names match!!!!
                cancelList[vname] = 1;
                if (Function *rdyFunc = ruleRDYFunction[func]) {
                    std::string fname = name + "__" + iitem.first;
                    std::string rname = name + "__" + pushSeen[rdyFunc];
                    fprintf(OStr, ", %s, %s", rname.c_str(), fname.c_str());
                    prefix = ",";
                }
            }
            fprintf(OStr, ")");
        }
        fprintf(OStr, " {\n");
        for (auto item: table->interfaceConnect)
            fprintf(OStr, "    %s = &%s;\n", item.target.c_str(), item.source.c_str());
        fprintf(OStr, "  }\n");
    }
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string mname = FI.first;
        if (!cancelList[mname])
        fprintf(OStr, "  %s { %s; }\n", printFunctionSignature(func, mname, false).c_str(),
            printFunctionInstance(func, name + "__" + mname, "this").c_str());
    }
    for (auto item: table->interfaces)
        fprintf(OStr, "  void set%s(%s) { %s = v; }\n", item.first.c_str(),
            printType(item.second, false, "v", "", "", false).c_str(), item.first.c_str());
    }
    fprintf(OStr, "}%s;\n#endif  // __%s_H__\n", (name.substr(0,12) == "l_struct_OC_" ? name.c_str():""), name.c_str());
    fclose(OStr);

    // now generate '.cpp' file
    if (name.substr(0,12) != "l_struct_OC_" && !inInterface) {
    OStr = fopen((oDir + "/" + name + ".cpp").c_str(), "w");
    fprintf(OStr, "#include \"%s.h\"\n", name.c_str());
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string mname = FI.first;
        fprintf(OStr, "%s {\n", printFunctionSignature(func, name + "__" + mname, true).c_str());
        auto AI = func->arg_begin();
        std::string argt = printType(AI->getType(), /*isSigned=*/false, "", "", "", false);
        fprintf(OStr, "        %s thisp = (%s)thisarg;\n", argt.c_str(), argt.c_str());
        processFunction(func);
        for (auto info: declareList)
            fprintf(OStr, "        %s;\n", info.second.c_str());
        for (auto info: storeList) {
            if (Value *cond = getCondition(info.cond, 0))
                fprintf(OStr, "        if (%s) {\n    ", printOperand(cond, false).c_str());
            if (info.target.substr(0, 7) == "thisp->" && table->shadow[info.target.substr(7)]) {
                // State element updates are written to shadow variables so that changes
                // in state are not visible until 'commit()' method is called.
                fprintf(OStr, "        %s_shadow = %s;\n", info.target.c_str(), info.item.c_str());
                fprintf(OStr, "        %s_valid = 1;\n", info.target.c_str());
            }
            else
            fprintf(OStr, "        %s = %s;\n", info.target.c_str(), info.item.c_str());
            if (getCondition(info.cond, 0))
                fprintf(OStr, "        }\n    ");
        }
        for (auto info: functionList) {
            if (Value *cond = getCondition(info.cond, 0))
                fprintf(OStr, "        if (%s)\n    ", printOperand(cond, false).c_str());
            fprintf(OStr, "        %s;\n", info.item.c_str());
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
    fprintf(OStr, "    commit();\n");
    fprintf(OStr, "}\n");
    // Generate 'commit()' method to copy values from shadow variable into state elements
    fprintf(OStr, "void %s::commit()\n{\n", name.c_str());
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
        if (fname != "" && !dyn_cast<StructType>(element) && !dyn_cast<PointerType>(element)) {
            fprintf(OStr, "    if (%s_valid) %s = %s_shadow;\n", fname.c_str(), fname.c_str(), fname.c_str());
            fprintf(OStr, "    %s_valid = 0;\n", fname.c_str());
        }
    }
    for (auto item : runLines)
        fprintf(OStr, "    %s.commit();\n", item.c_str());
    fprintf(OStr, "}\n");
    fclose(OStr);
    }
}
