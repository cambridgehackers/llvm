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
#include "llvm/ADT/StringExtras.h"

using namespace llvm;

#include "AtomiccDecl.h"

static int dontInlineValues;//=1;

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

static void setAssign(std::string target, std::string value)
{
     assignList[target] = inlineValue(value, true);
}

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(FILE *OStr, ModuleIR *IR, std::string instance)
{
    std::list<std::string> modulePortList, wireList;
    std::string inp = "input ", outp = "output ", instPrefix, inpClk = "input ";

//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, IR->name.c_str(), instance.c_str());
    if (instance != "") {
        instPrefix = instance + MODULE_SEPARATOR;
        inp = instPrefix;
        outp = instPrefix;
        inpClk = "";
    }
    modulePortList.push_back(inpClk + "CLK");
    modulePortList.push_back(inpClk + "nRST");
    // First handle all 'incoming' interface methods
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = IR->method[methodName];
        if (IR->ruleFunctions[methodName.substr(0, methodName.length()-5)])
            continue;
        std::string wparam = inp + methodName;
        if (instance != "") {
            // define 'wire' elements before instantiating instance
            if (inlineValue(wparam, false) == "")
                wireList.push_back(MI->retArrRange + wparam);
            wparam = inlineValue(wparam, true);
        }
        else if (!MI->action)
            wparam = outp + MI->retArrRange + methodName;
        modulePortList.push_back(wparam);
        for (auto item: MI->params) {
            if (instance != "") {
                // define 'wire' elements before instantiating instance
                wparam = inp + item.name;
                if (inlineValue(wparam, false) == "")
                    wireList.push_back(item.arrRange + wparam);
                wparam = inlineValue(wparam, true);
            }
            else
                wparam = inp + item.arrRange + item.name;
            modulePortList.push_back(wparam);
        }
    }

    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    for (auto oitem: IR->outcall)
        for (auto FI : oitem.IR->method) {
            MethodInfo *MI = oitem.IR->method[FI.first];
            modulePortList.push_back((MI->action ? outp : inp + (instance == "" ? MI->retArrRange :""))
                + oitem.fldName + MODULE_SEPARATOR + FI.first);
            for (auto item: MI->params)
                modulePortList.push_back(outp + (instance == "" ? item.arrRange :"")
                   + oitem.fldName + MODULE_SEPARATOR + item.name);
        }

    // now write actual module signature to output file
    for (auto wname: wireList)
        fprintf(OStr, "    wire %s;\n", wname.c_str());
    if (instance != "")
        fprintf(OStr, "    %s %s (\n", IR->name.c_str(), instance.c_str());
    else
        fprintf(OStr, "module %s (\n", IR->name.c_str());
    for (auto PI = modulePortList.begin(); PI != modulePortList.end();) {
        if (instance != "")
            fprintf(OStr, "    ");
        fprintf(OStr, "    %s", PI->c_str());
        PI++;
        if (PI != modulePortList.end())
            fprintf(OStr, ",\n");
    }
    fprintf(OStr, ");\n");
    for (auto item: IR->softwareName) {
        fprintf(OStr, "// software: %s\n", item.first.c_str());
    }
}

typedef struct {
    std::string fname;
    std::string value;
} MuxValueEntry;

typedef struct {
    std::string fname;
    std::string signal;
} MuxEnableEntry;
/*
 * Generate *.v and *.vh for a Verilog module
 */
void generateModuleDef(ModuleIR *IR, FILE *OStr)
{
    std::list<std::string> alwaysLines, resetList;
    // 'Or' together ENA lines from all invocations of a method from this class
    std::list<MuxEnableEntry> muxEnableList;
    // 'Mux' together parameter settings from all invocations of a method from this class
    std::map<std::string, std::list<MuxValueEntry>> muxValueList;

    assignList.clear();
    lateAssignList.clear();
    generateModuleSignature(OStr, IR, "");
    for (auto IC : IR->interfaceConnect) {
        for (auto FI : IC.IR->method) {
            setAssign(IC.target + MODULE_SEPARATOR + FI.first,
                      IC.source + MODULE_SEPARATOR + FI.first);
        }
    }
    // generate local state element declarations
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = IR->method[methodName];
        std::string rdyName = methodName.substr(0, methodName.length()-5) + "__RDY";
        if (endswith(methodName, "__VALID"))
            rdyName = methodName.substr(0, methodName.length()-7) + "__READY";
        std::list<std::string> localStore;
        for (auto info: IR->method[methodName]->storeList) {
            if (info.isAlloca)
                setAssign(info.dest, cleanupValue(info.value));
            else {
                if (info.cond != "")
                    localStore.push_back("    if (" + info.cond + ")");
                localStore.push_back("    " + info.dest + " <= " + info.value + ";");
            }
        }
        for (auto info: IR->method[methodName]->callList) {
            std::string tempCond = methodName + "_internal" + info.cond;
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string calledName = rval.substr(0, ind);
            rval = rval.substr(ind+1);
            rval = cleanupValue(rval.substr(0, rval.length()-1));
            if (info.isAction)
                muxEnableList.push_back(MuxEnableEntry{tempCond, calledName});
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
                muxValueList[rval].push_back(MuxValueEntry{tempCond, paramValue});
                rval = rest;
            }
        }
        if (!MI->action) {
            if (methodName == rdyName)
                assignList[methodName + "_internal"] = IR->method[methodName]->guard;  // collect the text of the return value into a single 'assign'
            else if (IR->method[methodName]->guard != "")
                setAssign(methodName, IR->method[methodName]->guard);  // collect the text of the return value into a single 'assign'
        }
        else if (!IR->ruleFunctions[methodName.substr(0, methodName.length()-5)]) {
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
        if (assignList[item.signal] != "")
            assignList[item.signal] += " || ";
        assignList[item.signal] += item.fname;
    }
    // combine mux'ed assignments into a single 'assign' statement
    // Context: before local state declarations, to allow inlining
    for (auto item: muxValueList) {
        int remain = item.second.size();
        std::string temp;
        for (auto element: item.second) {
            std::string tempCond = element.fname;
            if (--remain)
                temp += tempCond + " ? ";
            temp += element.value;
            if (remain)
                temp += " : ";
        }
        setAssign(item.first, temp);
    }
    // generate local state element declarations
    for (auto item: IR->fields) {
         if (item.typeStr != "") {
             fprintf(OStr, "    %s;\n", item.typeStr.c_str());
             resetList.push_back(item.fldName);
         }
         else if (item.iIR) {
             if (item.iIR->name.substr(0,12) == "l_struct_OC_") {
                 fprintf(OStr, "    reg%s %s;\n", item.arrRange.c_str(), item.fldName.c_str());
                 resetList.push_back(item.fldName);
             }
             else if (item.iIR->name.substr(0, 12) != "l_ainterface")
                 generateModuleSignature(OStr, item.iIR, item.fldName);
         }
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
