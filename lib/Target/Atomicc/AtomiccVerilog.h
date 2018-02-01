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
#include "AtomiccIR.h"

static int dontInlineValues;//=1;
std::map<std::string, bool> inList, outList;
std::map<std::string, std::string> assignList;
std::map<std::string, std::string> wireList; // name -> type

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
static std::string inlineValue(std::string wname, std::string atype)
{
    std::string temp = assignList[wname], exactMatch;
//printf("[%s:%d] assignList[%s] = %s\n", __FUNCTION__, __LINE__,wname.c_str(), temp.c_str());
    if (temp != "") {
        assignList[wname] = "";
        return temp;
    }
    if (!dontInlineValues) {
        int referenceCount = 0;
        for (auto item: assignList) {
            if (item.second == wname)
                exactMatch = item.first;
            if (findExact(item.second, wname))
                referenceCount++;
        }
        if (referenceCount == 1 && exactMatch != "") {
printf("[%s:%d] inlinewname %s exactMatch %s out %d\n", __FUNCTION__, __LINE__, wname.c_str(), exactMatch.c_str(), outList[exactMatch]);
if (!outList[exactMatch] || atype != "") {
            assignList[exactMatch] = "";
            return exactMatch;
}
        }
    }
    // define 'wire' elements before instantiating instance
    if (atype != "")
        wireList[wname] = atype;
    return wname;
}

static void setAssign(std::string target, std::string value)
{
//printf("[%s:%d] [%s] = %s\n", __FUNCTION__, __LINE__, target.c_str(), value.c_str());
     if (!outList[target])
         printf("[%s:%d] ASSIGNNONONONONONNO %s = %s\n", __FUNCTION__, __LINE__, target.c_str(), value.c_str());
     assignList[target] = inlineValue(value, "");
}

static std::string sizeProcess(std::string type)
{
    uint64_t val = convertType(type);
    if (val > 1)
        return "[" + autostr(val - 1) + ":0]";
    return "";
}

static void setDir(std::string name, bool out)
{
    if (out)
        outList[name] = true;
    else
        inList[name] = true;
}

static void generateModuleSignatureList(ModuleIR *IR, std::string instance)
{
    std::string instPrefix;
    if (instance != "")
        instPrefix = instance + MODULE_SEPARATOR;
    // First handle all 'incoming' interface methods
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = IR->method[methodName];
        std::string wparam = instPrefix + methodName;
        //if (MI->rule)
            //continue;
        if (instance != "")
            setDir(wparam, MI->type == ""); // action -> out
        else
            setDir(wparam, MI->type != ""); // !action -> out
        wparam = wparam.substr(0, wparam.length()-5) + MODULE_SEPARATOR;
        for (auto item: MI->params)
            setDir(wparam + item.name, instance != "");
    }
    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    for (auto oitem: IR->outcall)
        for (auto FI : oitem.IR->method) {
            MethodInfo *MI = oitem.IR->method[FI.first];
            std::string wparam = oitem.fldName + MODULE_SEPARATOR + FI.first;
            setDir(wparam, MI->type == ""); // action -> out
            wparam = wparam.substr(0, wparam.length()-5) + MODULE_SEPARATOR;
            for (auto item: MI->params)
                setDir(wparam + item.name, instance == "");
        }

}

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(FILE *OStr, ModuleIR *IR, std::string instance)
{
    std::list<std::string> modulePortList;
    std::string inp = "input ", outp = "output ", instPrefix, inpClk = "input ";

    auto checkWire = [&](std::string wparam, std::string atype, std::string dir) -> void {
        std::string ret = inp + wparam;
        if (instance != "")
            ret = inlineValue(ret, atype);
        else if (atype != "") // !action
            ret = dir + sizeProcess(atype) + wparam;
        modulePortList.push_back(ret);
      };
//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, IR->name.c_str(), instance.c_str());
    wireList.clear();
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
        if (!MI->rule) {
            checkWire(methodName, MI->type, outp);
            for (auto item: MI->params)
                checkWire(methodName.substr(0, methodName.length()-5) + MODULE_SEPARATOR + item.name, item.type, inp);
        }
    }

    auto sizeT = [&](std::string atype) -> std::string {
        if (instance == "")
            return sizeProcess(atype);
        return "";
    };
    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    for (auto oitem: IR->outcall)
        for (auto FI : oitem.IR->method) {
            MethodInfo *MI = oitem.IR->method[FI.first];
            std::string wparam = oitem.fldName + MODULE_SEPARATOR + FI.first;
            modulePortList.push_back((MI->type == ""/* action */ ? outp : inp + sizeT(MI->type)) + wparam);
            wparam = wparam.substr(0, wparam.length()-5) + MODULE_SEPARATOR;
            for (auto item: MI->params)
                modulePortList.push_back(outp + sizeT(item.type) + wparam + item.name);
        }

    // now write actual module signature to output file
    for (auto item: wireList)
        if (item.second != "")
        fprintf(OStr, "    wire %s;\n", (sizeProcess(item.second) + item.first).c_str());
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
        fprintf(OStr, "// software: %s\n", item.c_str());
    }
}
MethodInfo *lookupQualName(ModuleIR *searchIR, std::string searchStr)
{
    while (searchStr != "") {
        int ind = searchStr.find(MODULE_SEPARATOR);
        if (ind < 0)
            break;
        std::string temp = searchStr.substr(0, ind);
        for (auto item: searchIR->fields) {
//printf("[%s:%d] prev %s/%d searchfor %s in %s : %s %p\n", __FUNCTION__, __LINE__, searchStr.c_str(), ind, temp.c_str(), searchIR->name.c_str(), item.fldName.c_str(), item.IR);
            int64_t vecCount = item.vecCount;
            int dimIndex = 0;
            do {
                std::string fldName = item.fldName;
                if (vecCount != -1)
                    fldName += autostr(dimIndex++);
                if (fldName == temp) {
                    searchIR = item.IR;
                    goto nextItem;
                }
            } while(vecCount-- > 0);
        }
        break;
nextItem:
        searchStr = searchStr.substr(ind+1);
    }
    MethodInfo *MI = searchIR->method[searchStr];
    if (!MI) {
        printf("[%s:%d] method %s not found in module %s\n", __FUNCTION__, __LINE__, searchStr.c_str(), searchIR->name.c_str());
        exit(-1);
    }
    return MI;
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
    inList.clear();
    outList.clear();
    generateModuleSignatureList(IR, "");
    for (auto item: IR->fields) {
        int64_t vecCount = item.vecCount;
        int dimIndex = 0;
        do {
            std::string fldName = item.fldName;
            if (vecCount != -1)
                fldName += autostr(dimIndex++);
            if (item.IR && !item.isPtr)
            if (item.IR->name.substr(0,12) != "l_struct_OC_")
            if (item.IR->name.substr(0, 12) != "l_ainterface")
                generateModuleSignatureList(item.IR, fldName);
        } while(vecCount-- > 0);
    }

    // Generate module header
    generateModuleSignature(OStr, IR, "");
    for (auto IC : IR->interfaceConnect)
        for (auto FI : IC.IR->method)
            setAssign(IC.target + MODULE_SEPARATOR + FI.first,
                      IC.source + MODULE_SEPARATOR + FI.first);
    // generate local state element declarations
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = IR->method[methodName];
        std::list<std::string> localStore;
        for (auto info: MI->storeList) {
            std::string rval = cleanupValue(info.value);
            if (info.isAlloca)
                setAssign(info.dest, cleanupValue(info.value));
            else {
                if (info.cond != "")
                    localStore.push_back("    if (" + info.cond + ")");
                localStore.push_back("    " + info.dest + " <= " + rval + ";");
            }
        }
        for (auto info: MI->callList) {
            std::string tempCond = info.cond;
            if (tempCond != "")
                tempCond = " & " + tempCond;
            tempCond = methodName + tempCond;
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string calledName = rval.substr(0, ind);
            rval = rval.substr(ind+1);
            rval = cleanupValue(rval.substr(0, rval.length()-1));
            if (info.isAction)
                muxEnableList.push_back(MuxEnableEntry{tempCond, calledName});
            auto CI = lookupQualName(IR, calledName);
            auto AI = CI->params.begin();
            std::string pname = calledName.substr(0, calledName.length()-5) + MODULE_SEPARATOR;
            while(rval.length()) {
                std::string rest;
                int ind = rval.find(",");
                if (ind > 0) {
                    rest = rval.substr(ind+1);
                    rval = rval.substr(0, ind);
                }
                muxValueList[pname + AI->name].push_back(MuxValueEntry{tempCond, rval});
                rval = rest;
                AI++;
            }
        }
        if (MI->guard != "")
            setAssign(methodName, MI->guard);  // collect the text of the return value into a single 'assign'
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
        int64_t vecCount = item.vecCount;
        int dimIndex = 0;
        do {
            std::string fldName = item.fldName;
            if (vecCount != -1)
                fldName += autostr(dimIndex++);
            uint64_t size = convertType(item.type);
            if (item.IR && !item.isPtr) {
                if (item.IR->name.substr(0,12) == "l_struct_OC_") {
                    fprintf(OStr, "    reg%s %s;\n", sizeProcess(item.type).c_str(), fldName.c_str());
                    resetList.push_back(fldName);
                }
                else if (item.IR->name.substr(0, 12) != "l_ainterface")
                    generateModuleSignature(OStr, item.IR, fldName);
            }
            else if (size != 0) {
                std::string temp = "    reg";
                if (size > 8)
                    temp += "[" + autostr(size - 1) + ":0]";
                temp += " " + fldName;
                if (item.arrayLen > 0)
                    temp += "[" + autostr(item.arrayLen) + ":0]";
                temp += ";\n";
                fprintf(OStr, "%s", temp.c_str());
                resetList.push_back(fldName);
            }
        } while(vecCount-- > 0);
    }
    // generate 'assign' items
    for (auto item: outList)
        if (item.second) {
            if (assignList[item.first] != "")
                fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), assignList[item.first].c_str());
            //else
                //fprintf(OStr, "    assign %s = MISSING_ASSIGNMENT_FOR_OUTPUT_VALUE;\n", item.first.c_str());
            assignList[item.first] = "";
        }
    bool seen = false;
    for (auto item: assignList)
        if (item.second != "") {
            if (!seen)
                fprintf(OStr, "    // Extra assigments, not to output wires\n");
            seen = true;
            fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), item.second.c_str());
        }
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
