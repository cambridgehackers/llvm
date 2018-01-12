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
        return 0;
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
std::map<std::string, std::string> assignList, lateAssignList;
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

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(FILE *OStr, const StructType *STy, std::string instance)
{
    std::list<std::string> modulePortList, wireList;
    ClassMethodTable *table = getClass(STy);
    std::string topClassName = getStructName(STy);
    std::string inp = "input ", outp = "output ", instPrefix, inpClk = "input ";

//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, topClassName.c_str(), instance.c_str());
    if (instance != "") {
        instPrefix = instance + MODULE_SEPARATOR;
        inp = instPrefix;
        outp = instPrefix;
        inpClk = "";
    }
    modulePortList.push_back(inpClk + "CLK");
    modulePortList.push_back(inpClk + "nRST");
    // First handle all 'incoming' interface methods
    for (auto FI : table->method) {
        std::string methodName = FI.first;
        if (table->ruleFunctions[methodName.substr(0, methodName.length()-5)])
            continue;
        const Function *func = FI.second;
        Type *retType = func->getReturnType();
        std::string wparam = inp + methodName;
        std::string arrRange = verilogArrRange(retType);
        auto AI = func->arg_begin(), AE = func->arg_end();
        if (instance != "") {
            // define 'wire' elements before instantiating instance
            if (inlineValue(wparam, false) == "")
                wireList.push_back(arrRange + wparam);
            wparam = inlineValue(wparam, true);
        }
        else if (!isActionMethod(func))
            wparam = outp + arrRange + methodName;
        modulePortList.push_back(wparam);
        for (AI++; AI != AE; ++AI) {
            arrRange = verilogArrRange(AI->getType());
            if (instance != "") {
                // define 'wire' elements before instantiating instance
                wparam = inp + AI->getName().str();
                if (inlineValue(wparam, false) == "")
                    wireList.push_back(arrRange + wparam);
                wparam = inlineValue(wparam, true);
            }
            else
                wparam = inp + arrRange + AI->getName().str();
            modulePortList.push_back(wparam);
        }
    }

    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        std::string fldName = fieldName(STy, Idx);
        Type *element = *I;
        if (Type *newType = table->replaceType[Idx])
            element = newType;
        const PointerType *PTy = dyn_cast<PointerType>(element);
        if (fldName == "" || !PTy)
            continue;
        const StructType *iSTy = dyn_cast<StructType>(PTy->getElementType());
        if (!isInterface(iSTy))
            continue;
//printf("[%s:%d] indication interface topname %s sname %s fldName %s\n", __FUNCTION__, __LINE__, STy->getName().str().c_str(), iSTy->getName().str().c_str(), fldName.c_str());
iSTy->dump();
        std::string elementName = fldName + MODULE_SEPARATOR;
        ClassMethodTable *itable = getClass(iSTy);
//printf("[%s:%d] indication interface topname %s sname %s elementName %s\n", __FUNCTION__, __LINE__, STy->getName().str().c_str(), iSTy->getName().str().c_str(), elementName.c_str());
        for (auto FI : itable->method) {
            std::string wparam = outp;
            Function *func = FI.second;
            auto AI = func->arg_begin(), AE = func->arg_end();
printf("[%s:%d] methodName %s func %p\n", __FUNCTION__, __LINE__, FI.first.c_str(), func);
            if (!isActionMethod(func))
                wparam = inp + (instance == "" ? verilogArrRange(func->getReturnType()):"");
            modulePortList.push_back(wparam + elementName + FI.first);
            for (AI++; AI != AE; ++AI) {
                modulePortList.push_back(outp
                   + (instance == "" ? verilogArrRange(AI->getType()):"")
                   + elementName + AI->getName().str());
            }
        }
    }

    // now write actual module signature to output file
    for (auto wname: wireList)
        fprintf(OStr, "    wire %s;\n", wname.c_str());
    if (instance != "")
        fprintf(OStr, "    %s %s (\n", topClassName.c_str(), instance.c_str());
    else
        fprintf(OStr, "module %s (\n", topClassName.c_str());
    for (auto PI = modulePortList.begin(); PI != modulePortList.end();) {
        if (instance != "")
            fprintf(OStr, "    ");
        fprintf(OStr, "    %s", PI->c_str());
        PI++;
        if (PI != modulePortList.end())
            fprintf(OStr, ",\n");
    }
    fprintf(OStr, ");\n");
    for (auto item: table->softwareName) {
        fprintf(OStr, "// software: %s\n", item.first.c_str());
    }
}

std::string cleanupValue(std::string arg)
{
    int ind;
    while((ind = arg.find("{}")) > 0)
        arg = arg.substr(0, ind) + arg.substr(ind+2); // remove '{}'
    return arg;
}

/*
 * Generate *.v and *.vh for a Verilog module
 */
void generateModuleDef(const StructType *STy, FILE *OStr)
{
    std::list<std::string> alwaysLines, resetList;
    std::string name = getStructName(STy);
    ClassMethodTable *table = getClass(STy);
    // 'Or' together ENA lines from all invocations of a method from this class
    std::list<MuxEnableEntry> muxEnableList;
    // 'Mux' together parameter settings from all invocations of a method from this class
    std::map<std::string, std::list<MuxValueEntry>> muxValueList;

    assignList.clear();
    lateAssignList.clear();
    generateModuleSignature(OStr, STy, "");
    for (auto IC : table->interfaceConnect) {
        ClassMethodTable *mtable = getClass(IC.STy);
        for (auto FI : mtable->method) {
            setAssign(IC.target + MODULE_SEPARATOR + FI.first,
                      IC.source + MODULE_SEPARATOR + FI.first);
        }
    }
    // generate local state element declarations
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : table->method) {
        Function *func = FI.second;
        std::string methodName = FI.first;
        std::string rdyName = methodName.substr(0, methodName.length()-5) + "__RDY";
        if (endswith(methodName, "__VALID"))
            rdyName = methodName.substr(0, methodName.length()-7) + "__READY";
        std::list<std::string> localStore;
        for (auto info: storeList[func]) {
            std::string pdest = printOperand(info->getPointerOperand(), true);
            std::string pvalue = printOperand(info->getOperand(0), false);
            if (pdest[0] == '&')
                pdest = pdest.substr(1);
            if (isAlloca(info->getPointerOperand()))
                setAssign(pdest, cleanupValue(pvalue));
            else {
                if (Value *cond = getCondition(info->getParent(), 0))
                    localStore.push_back("    if (" + printOperand(cond, false) + ")");
                localStore.push_back("    " + pdest + " <= " + pvalue + ";");
            }
        }
        for (auto info: callList[func]) {
            std::string rval = printCall(info); // get call info
            int ind = rval.find("{");
            std::string calledName = rval.substr(0, ind);
            rval = rval.substr(ind+1);
            rval = cleanupValue(rval.substr(0, rval.length()-1));
            Function *cfunc = info->getCalledFunction();
            if (isActionMethod(cfunc))
                muxEnableList.push_back(MuxEnableEntry{methodName + "_internal", info->getParent(), calledName});
            while(rval.length()) {
                std::string rest;
                int ind = rval.find(",");
                if (ind > 0) {
                    rest = rval.substr(ind+1);
                    rval = rval.substr(0, ind);
                }
                ind = rval.find(";");
                std::string paramValue;
                if (ind > 0) {
                    paramValue = rval.substr(ind+1);
                    rval = rval.substr(0, ind);
                }
                muxValueList[rval].push_back(
                    MuxValueEntry{methodName + "_internal", info->getParent(), paramValue});
                rval = rest;
            }
        }
        table->guard[func] = cleanupValue(table->guard[func]);
        if (!isActionMethod(func)) {
            if (ruleENAFunction[func])
                assignList[methodName + "_internal"] = table->guard[func];  // collect the text of the return value into a single 'assign'
            else if (table->guard[func] != "")
                setAssign(methodName, table->guard[func]);  // collect the text of the return value into a single 'assign'
        }
        else if (!table->ruleFunctions[methodName.substr(0, methodName.length()-5)]) {
            // generate RDY_internal wire so that we can reference RDY expression inside module
            fprintf(OStr, "    wire %s_internal;\n", rdyName.c_str());
            lateAssignList[rdyName] = rdyName + "_internal";
        }
        if (localStore.size()) {
            alwaysLines.push_back("if (" + methodName + ") begin");
            alwaysLines.splice(alwaysLines.end(), localStore);
            alwaysLines.push_back("end; // End of " + methodName);
        }
    }
    for (auto item: muxEnableList) {
        std::string tempCond = item.fname;
        if (Value *cond = getCondition(item.bb, 0))
            tempCond += " & " + printOperand(cond, false);
        if (assignList[item.signal] != "")
            assignList[item.signal] += " || ";
        assignList[item.signal] += tempCond;
    }
    // combine mux'ed assignments into a single 'assign' statement
    // Context: before local state declarations, to allow inlining
    for (auto item: muxValueList) {
        int remain = item.second.size();
        std::string temp;
        for (auto element: item.second) {
            std::string tempCond = element.fname;
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
        std::string fldName = fieldName(STy, Idx);
        if (fldName != "") {
            if (vecCount != -1)
                fldName += utostr(dimIndex++);
            if (const StructType *STy = dyn_cast<StructType>(element)) {
                std::string structName = getStructName(STy);
                if (structName.substr(0,12) == "l_struct_OC_") {
                    fprintf(OStr, "    reg%s %s;\n", verilogArrRange(element).c_str(), fldName.c_str());
                    resetList.push_back(fldName);
                }
                else if (!isInterface(STy))
                    generateModuleSignature(OStr, STy, fldName);
            }
            else if (!dyn_cast<PointerType>(element)) {
                fprintf(OStr, "    %s;\n", printType(element, false, fldName, "", "", false).c_str());
                resetList.push_back(fldName);
            }
        }
        } while(vecCount-- > 0);
    }
    // generate 'assign' items
    for (auto item: assignList)
        if (item.second != "")
            fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), item.second.c_str());
    for (auto item: lateAssignList)
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
