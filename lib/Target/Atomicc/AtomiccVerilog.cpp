//===-- AtomiccVerilog.cpp - Generating Verilog from LLVM -----===//
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
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;

#include "AtomiccDecl.h"

static int dontInlineValues;//=1;

static uint64_t sizeType(Type *Ty)
{
    //const DataLayout *TD = EE->getDataLayout();
    switch (Ty->getTypeID()) {
    case Type::IntegerTyID:
        return cast<IntegerType>(Ty)->getBitWidth();
    case Type::StructTyID: {
        //unsigned NumBits = TD->getTypeAllocSize(Ty) * 8;
        const StructType *STy = cast<StructType>(Ty);
        uint64_t len = 0;
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            if (fieldName(STy, Idx) != "")
                len += sizeType(*I);
        }
        return len;
        }
    case Type::ArrayTyID: {
        ArrayType *ATy = cast<ArrayType>(Ty);
        unsigned len = ATy->getNumElements();
        if (len == 0) len = 1;
        return len * sizeType(ATy->getElementType());
        }
    case Type::PointerTyID:
        return sizeType(cast<PointerType>(Ty)->getElementType());
    case Type::VoidTyID:
    case Type::FunctionTyID:
    default:
        llvm_unreachable("Unhandled case in sizeType!");
    }
}

std::string verilogArrRange(Type *Ty)
{
    uint64_t NumBits = sizeType(Ty);

    if (NumBits > 1)
        return "[" + utostr(NumBits - 1) + ":0]";
    return "";
}
static bool findExact(std::string haystack, std::string needle)
{
    std::string::size_type sz = haystack.find(needle);
    if (sz == std::string::npos || needle == "")
        return false;
    sz += needle.length();
    if (isalnum(haystack[sz]) || haystack[sz] == '_' || haystack[sz] == '$')
        return findExact(haystack.substr(sz), needle);
    return true;
}

/*
 * lookup/replace values for class variables that are assigned only 1 time.
 */
std::map<std::string, std::string> assignList;
static std::string inlineValue(std::string wname, bool clear)
{
    std::string temp, exactMatch;
    if (!dontInlineValues && (temp = assignList[wname]) == "") {
        int referenceCount = 0;
        for (auto item: assignList) {
            if (item.second == wname)
                exactMatch = item.first;
            if (findExact(item.second, wname))
                referenceCount++;
        }
        if (referenceCount == 1 && exactMatch != "") {
            if (clear)
                assignList[exactMatch] = "";
            return exactMatch;
        }
    }
    if (clear) {
        if (temp != "")
            assignList[wname] = "";
        else
            return wname;
    }
    return temp;
}

void setAssign(std::string target, std::string value)
{
     assignList[target] = inlineValue(value, true);
}

void buildPrefix(ClassMethodTable *table, PrefixType &interfacePrefix)
{
    for (auto item: table->interfaceList) {
        ClassMethodTable *itable = classCreate[item.STy];
//printf("[%s:%d] prefix %s count %d\n", __FUNCTION__, __LINE__, item.name.c_str(), (int)itable->method.size());
        for (auto iitem: itable->method) {
            //Function *func = iitem.second;
            std::string mname = iitem.first;
            interfacePrefix[mname] = item.name + "$";
            interfacePrefix[mname + "__ENA"] = item.name + "$";
            interfacePrefix[mname + "__VALID"] = item.name + "$";
//printf("[%s:%d] class %s name %s prefix %s\n", __FUNCTION__, __LINE__, table->STy->getName().str().c_str(), getMethodName(func->getName()).c_str(), item.name.c_str());
        }
    }
}
/*
 * Generate verilog module header for class definition or reference
 */
void generateModuleSignature(FILE *OStr, const StructType *STy, std::string instance)
{
    ClassMethodTable *table = classCreate[STy];
    std::string name = getStructName(STy);
    std::string inp = "input ", outp = "output ", instPrefix, inpClk = "input ";
    std::list<std::string> paramList;
    PrefixType interfacePrefix;
//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, name.c_str(), instance.c_str());
    buildPrefix(table, interfacePrefix);
    if (instance != "") {
        instPrefix = instance + MODULE_SEPARATOR;
        inp = instPrefix;
        outp = instPrefix;
        inpClk = "";
        for (auto FI : table->method) {
            const Function *func = FI.second;
            std::string mname = interfacePrefix[FI.first] + pushSeen[func];
            Type *retType = func->getReturnType();
            auto AI = func->arg_begin(), AE = func->arg_end();
            std::string arrRange;
            std::string wparam = inp + mname;
            if (!isActionMethod(func))
                arrRange = verilogArrRange(retType);
            if (inlineValue(wparam, false) == "")
                fprintf(OStr, "    wire %s%s;\n", arrRange.c_str(), wparam.c_str());
            for (AI++; AI != AE; ++AI) {
                wparam = instPrefix + interfacePrefix[FI.first] + AI->getName().str();
                if (inlineValue(wparam, false) == "")
                    fprintf(OStr, "    wire %s%s;\n", verilogArrRange(AI->getType()).c_str(), wparam.c_str());
            }
        }
    }
    paramList.push_back(inpClk + "CLK");
    paramList.push_back(inpClk + "nRST");
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string mname = interfacePrefix[FI.first] + pushSeen[func];
        if (table->ruleFunctions[mname.substr(0, mname.length()-5)])
            continue;
        Type *retType = func->getReturnType();
        auto AI = func->arg_begin(), AE = func->arg_end();
        std::string wparam = inp + mname;
        if (instance != "")
            wparam = inlineValue(wparam, true);
        else if (!isActionMethod(func))
            wparam = outp + verilogArrRange(retType) + mname;
        paramList.push_back(wparam);
        for (AI++; AI != AE; ++AI) {
            if (instance != "")
                wparam = inlineValue(instPrefix + interfacePrefix[FI.first] + AI->getName().str(), true);
            else
                wparam = inp + verilogArrRange(AI->getType()) + interfacePrefix[FI.first] + AI->getName().str();
            paramList.push_back(wparam);
        }
    }
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        Type *element = *I;
        if (Type *newType = table->replaceType[Idx])
            element = newType;
        std::string fname = fieldName(STy, Idx);
        if (fname != "")
        if (const PointerType *PTy = dyn_cast<PointerType>(element)) {
            element = PTy->getElementType();
            if (const StructType *iSTy = dyn_cast<StructType>(element)) { // calling indications from this module
                if (ClassMethodTable *itable = classCreate[iSTy]) {
//printf("[%s:%d] indication interface topname %s sname %s fname %s\n", __FUNCTION__, __LINE__, STy->getName().str().c_str(), iSTy->getName().str().c_str(), fname.c_str());
                PrefixType interfacePrefix;
                buildPrefix(itable, interfacePrefix);
                for (auto FI : itable->method) {
                    Function *func = FI.second;
                    std::string wparam, mname = fname + MODULE_SEPARATOR + interfacePrefix[FI.first] + pushSeen[func];
//printf("[%s:%d] mname %s\n", __FUNCTION__, __LINE__, mname.c_str());
                    Type *retType = func->getReturnType();
                    auto AI = func->arg_begin(), AE = func->arg_end();
                    if (isActionMethod(func))
                        wparam = outp + mname;
                    else
                        wparam = inp + (instance == "" ? verilogArrRange(retType):"") + mname;
                    paramList.push_back(wparam);
                    for (AI++; AI != AE; ++AI) {
                        wparam = outp + (instance == "" ? verilogArrRange(AI->getType()):"") + baseMethod(mname) + "_" + interfacePrefix[FI.first] + AI->getName().str();
                        paramList.push_back(wparam);
                    }
                }
                }
            }
            else
                paramList.push_back(outp + printType(element, false, fname, "  ", "", false));
        }
    }
    if (instance != "")
        fprintf(OStr, "    %s %s (\n", name.c_str(), instance.c_str());
    else
        fprintf(OStr, "module %s (\n", name.c_str());
    for (auto PI = paramList.begin(); PI != paramList.end();) {
        if (instance != "")
            fprintf(OStr, "    ");
        fprintf(OStr, "    %s", PI->c_str());
        PI++;
        if (PI != paramList.end())
            fprintf(OStr, ",\n");
    }
    fprintf(OStr, ");\n");
}

std::string combineCondList(std::list<ReferenceType> &functionList)
{
    std::string temp, valsep;
    Value *prevCond = NULL;
    int remain = functionList.size();
    for (auto info: functionList) {
        remain--;
        temp += valsep;
        valsep = "";
        Value *opCond = getCondition(info.cond, 0);
        if (opCond && (remain || getCondition(info.cond, 1) != prevCond))
            temp += printOperand(opCond, false) + " ? ";
        temp += info.item;
        if (opCond && remain)
            valsep = " : ";
        prevCond = opCond;
    }
    return temp;
}

/*
 * Generate *.v and *.vh for a Verilog module
 */
void generateModuleDef(const StructType *STy, FILE *OStr)
{
    ClassMethodTable *table = classCreate[STy];
    std::string name = getStructName(STy);
    std::list<std::string> alwaysLines;
    std::string extraRules = utostr(table->ruleFunctions.size());
    std::list<std::string> resetList;

    assignList.clear();
    // first generate the verilog module file '.v'
    PrefixType interfacePrefix;
    buildPrefix(table, interfacePrefix);
    generateModuleSignature(OStr, STy, "");
    // generate local state element declarations
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string mname = interfacePrefix[FI.first] + pushSeen[func];
        std::string rdyName = mname.substr(0, mname.length()-5) + "__RDY";
        if (endswith(mname, "__VALID"))
            rdyName = mname.substr(0, mname.length()-7) + "__READY";
        std::string globalCondition = mname + "_internal";
        if (!isActionMethod(func)) {
            if (ruleENAFunction[func])
                assignList[globalCondition] = table->guard[func];  // collect the text of the return value into a single 'assign'
            else if (table->guard[func] != "")
                setAssign(mname, table->guard[func]);  // collect the text of the return value into a single 'assign'
        }
        else {
            // generate RDY_internal wire so that we can reference RDY expression inside module
            // generate ENA_internal wire that is and'ed with RDY_internal, so that we can
            // never be enabled unless we were actually ready.
            if (!table->ruleFunctions[mname.substr(0, mname.length()-5)]) {
                fprintf(OStr, "    wire %s_internal;\n", rdyName.c_str());
                fprintf(OStr, "    wire %s_internal = %s && %s_internal;\n", mname.c_str(), mname.c_str(), rdyName.c_str());
                assignList[rdyName] = rdyName + "_internal";
            }
            if (table->storeList[func].size() > 0) {
                alwaysLines.push_back("if (" + globalCondition + ") begin");
                for (auto info: table->storeList[func]) {
                    if (Value *cond = getCondition(info.cond, 0))
                        alwaysLines.push_back("    if (" + printOperand(cond, false) + ")");
                    alwaysLines.push_back("    " + info.target + " <= " + info.item + ";");
                }
                alwaysLines.push_back("end; // End of " + mname);
            }
        }
    }
    for (auto item: table->assignSavedList) {
        setAssign(item.target, item.value);
    }
    for (auto item: table->muxEnableList) {
        Function *func = item.bb->getParent();
        std::string tempCond = interfacePrefix[pushSeen[func]] + pushSeen[func] + "_internal";
        if (Value *cond = getCondition(item.bb, 0))
            tempCond += " & " + printOperand(cond, false);
        if (assignList[item.signal] != "")
            assignList[item.signal] += " || ";
        assignList[item.signal] += tempCond;
    }
    // combine mux'ed assignments into a single 'assign' statement
    // Context: before local state declarations, to allow inlining
    for (auto item: table->muxValueList) {
        int remain = item.second.size();
        std::string temp;
        for (auto element: item.second) {
            Function *func = element.bb->getParent();
            std::string tempCond = interfacePrefix[pushSeen[func]] + pushSeen[func] + "_internal";
            if (Value *cond = getCondition(element.bb, 0))
                tempCond += " & " + printOperand(cond, false);
            if (--remain)
                temp += tempCond + " ? ";
            temp += element.value;
            if (remain)
                temp += " : ";
        }
        setAssign(item.first, temp);
    }
    // generate local state element declarations
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        Type *element = *I;
        int64_t vecCount = -1;
        int dimIndex = 0;
        std::string vecDim;
        if (Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = table->replaceCount[Idx];
        }
        do {
        std::string fname = fieldName(STy, Idx);
        if (fname != "") {
            if (vecCount != -1)
                fname += utostr(dimIndex++);
            if (const StructType *STy = dyn_cast<StructType>(element)) {
                std::string sname = getStructName(STy);
                if (sname.substr(0,12) == "l_struct_OC_") {
                    fprintf(OStr, "    reg%s %s;\n", verilogArrRange(element).c_str(), fname.c_str());
                    resetList.push_back(fname);
                }
                else if (inheritsModule(STy, "class.BitsClass")) {
                    ClassMethodTable *table = classCreate[STy];
                    fprintf(OStr, "    reg[%s:0] %s;\n", table->instance.c_str(), fname.c_str());
                }
                else if (!inheritsModule(STy, "class.InterfaceClass"))
                    generateModuleSignature(OStr, STy, fname);
            }
            else if (!dyn_cast<PointerType>(element)) {
                fprintf(OStr, "    %s;\n", printType(element, false, fname, "", "", false).c_str());
                resetList.push_back(fname);
            }
        }
        } while(vecCount-- > 0);
    }
    // generate 'assign' items
    for (auto item: assignList)
        if (item.second != "")
            fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), item.second.c_str());
    // generate clocked updates to state elements
    if (resetList.size() > 0 || alwaysLines.size() > 0) {
        fprintf(OStr, "\n    always @( posedge CLK) begin\n      if (!nRST) begin\n");
        for (auto item: resetList)
            fprintf(OStr, "        %s <= 0;\n", item.c_str());
        fprintf(OStr, "      end // nRST\n");
        if (alwaysLines.size() > 0) {
            fprintf(OStr, "      else begin\n");
            for (auto info: alwaysLines)
                fprintf(OStr, "        %s\n", info.c_str());
            fprintf(OStr, "      end\n");
        }
        fprintf(OStr, "    end // always @ (posedge CLK)\n");
    }
    fprintf(OStr, "endmodule \n\n");
}
