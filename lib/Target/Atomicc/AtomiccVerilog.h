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
std::map<std::string, bool> inList, outList, seenList;
std::map<std::string, std::string> assignList;
std::map<std::string, std::string> wireList; // name -> type

typedef ModuleIR *(^CBFun)(FieldElement &item, std::string fldName);
#define CBAct ^ ModuleIR * (FieldElement &item, std::string fldName)
typedef struct {
    std::string cond;
    std::string value;
} MuxValueEntry;

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
        if (referenceCount == 1 && exactMatch != "" && (!outList[exactMatch] || atype != "")) {
            assignList[exactMatch] = "";
            return exactMatch;
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
    seenList[target] = true;
    assignList[target] = inlineValue(value, "");
}

static std::string sizeProcess(std::string type)
{
    uint64_t val = convertType(type);
    if (val > 1)
        return "[" + autostr(val - 1) + ":0]";
    return "";
}

static void setDir(std::string name, bool out, MethodInfo *MI)
{
    auto setItem = [&](std::string extra, bool oo) {
        if (oo)
            outList[name + extra] = true;
        else
            inList[name + extra] = true;
    };
    setItem("", out == (MI->type == ""));
    name = name.substr(0, name.length()-5) + MODULE_SEPARATOR;
    for (auto item: MI->params)
        setItem(item.name, out);
}

static ModuleIR *iterField(ModuleIR *IR, CBFun cbWorker)
{
    for (auto item: IR->fields) {
        int64_t vecCount = item.vecCount;
        int dimIndex = 0;
        do {
            std::string fldName = item.fldName;
            if (vecCount != -1)
                fldName += autostr(dimIndex++);
            if (auto ret = (cbWorker)(item, fldName))
                return ret;
        } while(--vecCount > 0);
    }
    return nullptr;
}

static MethodInfo *lookupQualName(ModuleIR *searchIR, std::string searchStr)
{
    while (1) {
        int ind = searchStr.find(MODULE_SEPARATOR);
        if (auto nextIR = iterField(searchIR, CBAct {
              if (ind != -1 && fldName == searchStr.substr(0, ind))
                  return item.IR;
              return nullptr; }))
            searchIR = nextIR;
        else
            return searchIR->method[searchStr];
        searchStr = searchStr.substr(ind+1);
    };
}

static void generateModuleSignatureList(ModuleIR *IR, std::string instance)
{
    // First handle all 'incoming' interface methods
    for (auto FI : IR->method) {
        MethodInfo *MI = IR->method[FI.first];
        if (!MI->rule || instance == "")
            setDir(instance + FI.first, instance != "", MI); // if !instance, !action -> out
    }
    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    for (auto oitem: IR->outcall)
        for (auto FI : oitem.IR->method) {
            MethodInfo *MI = oitem.IR->method[FI.first];
            if (!MI->rule)
                setDir(oitem.fldName + MODULE_SEPARATOR + FI.first, instance == "", MI); // action -> out
        }

}

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(FILE *OStr, ModuleIR *IR, std::string instance)
{
    std::list<std::string> modulePortList;
    std::string inp = "input ", outp = "output ", inpClk = "input ";

    auto checkWire = [&](std::string wparam, std::string atype, std::string dir) -> void {
        std::string ret = inp + wparam;
        if (instance != "")
            ret = inlineValue(ret, atype);
        else if (atype != "") // !action
            ret = dir + sizeProcess(atype) + wparam;
        modulePortList.push_back(ret);
    };
    auto sizeT = [&](std::string atype) -> std::string {
        if (instance == "")
            return sizeProcess(atype);
        return "";
    };
//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, IR->name.c_str(), instance.c_str());
    wireList.clear();
    if (instance != "") {
        inp = instance;
        outp = instance;
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
        fprintf(OStr, "    %s %s (\n", IR->name.c_str(), instance.substr(0,instance.length()-1).c_str());
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
    for (auto item: IR->softwareName)
        fprintf(OStr, "// software: %s\n", item.c_str());
}

/*
 * Generate *.v and *.vh for a Verilog module
 */
void generateModuleDef(ModuleIR *IR, FILE *OStr)
{
    __block std::list<std::string> alwaysLines, resetList;
    std::map<std::string, std::string> enableList;
    // 'Mux' together parameter settings from all invocations of a method from this class
    std::map<std::string, std::list<MuxValueEntry>> muxValueList;

    assignList.clear();
    inList.clear();
    outList.clear();
    generateModuleSignatureList(IR, "");
    iterField(IR, CBAct {
            if (item.IR && !item.isPtr)
            if (item.IR->name.substr(0,12) != "l_struct_OC_")
            if (item.IR->name.substr(0, 12) != "l_ainterface")
                generateModuleSignatureList(item.IR, fldName + MODULE_SEPARATOR);
          return nullptr;
          });

    // Generate module header
    generateModuleSignature(OStr, IR, "");
    for (auto IC : IR->interfaceConnect)
        for (auto FI : IC.IR->method) {
            std::string tstr = IC.target + MODULE_SEPARATOR + FI.first,
                        sstr = IC.source + MODULE_SEPARATOR + FI.first;
printf("[%s:%d] IFCCC %s/%d %s/%d\n", __FUNCTION__, __LINE__, tstr.c_str(), outList[tstr], sstr.c_str(), outList[sstr]);
            if (outList[sstr])
                setAssign(sstr, tstr);
            else
                setAssign(tstr, sstr);
            tstr = tstr.substr(0, tstr.length()-5) + MODULE_SEPARATOR;
            sstr = sstr.substr(0, sstr.length()-5) + MODULE_SEPARATOR;
            for (auto info: FI.second->params)
                setAssign(sstr + info.name, tstr + info.name);
        }
    // generate local state element declarations
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = IR->method[methodName];
        setAssign(methodName, MI->guard);  // collect the text of the return value into a single 'assign'
        bool alwaysSeen = false;
        for (auto info: MI->storeList) {
            std::string rval = cleanupValue(info.value);
            if (info.isAlloca)
                setAssign(info.dest, rval);
            else {
                if (!alwaysSeen)
                    alwaysLines.push_back("if (" + methodName + ") begin");
                alwaysSeen = true;
                if (info.cond != "")
                    alwaysLines.push_back("    if (" + info.cond + ")");
                alwaysLines.push_back("    " + info.dest + " <= " + rval + ";");
            }
        }
        if (alwaysSeen)
            alwaysLines.push_back("end; // End of " + methodName);
        for (auto info: MI->callList) {
            if (!info.isAction)
                continue;
            std::string tempCond = methodName;
            if (info.cond != "")
                tempCond += " & " + info.cond;
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string calledName = rval.substr(0, ind);
            rval = cleanupValue(rval.substr(ind+1, rval.length() - 1 - (ind+1)));
            // 'Or' together ENA lines from all invocations of a method from this class
            if (info.isAction)
                enableList[calledName] += " || " + tempCond;
            MethodInfo *CI = lookupQualName(IR, calledName);
            if (!CI) {
                printf("[%s:%d] method %s not found\n", __FUNCTION__, __LINE__, calledName.c_str());
                exit(-1);
            }
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
    }
    for (auto item: enableList)
        setAssign(item.first, item.second.substr(4) /* remove leading '||'*/);
    // combine mux'ed assignments into a single 'assign' statement
    // Context: before local state declarations, to allow inlining
    for (auto item: muxValueList) {
        std::string temp, prevCond, prevValue;
        for (auto element: item.second) {
            if (prevCond != "")
                temp += prevCond + " ? " + prevValue + " : ";
            prevCond = element.cond;
            prevValue = element.value;
        }
        setAssign(item.first, temp + prevValue);
    }
    // generate local state element declarations
    iterField(IR, CBAct {
            uint64_t size = convertType(item.type);
            if (item.IR && !item.isPtr) {
                if (item.IR->name.substr(0,12) == "l_struct_OC_") {
                    fprintf(OStr, "    reg%s %s;\n", sizeProcess(item.type).c_str(), fldName.c_str());
                    resetList.push_back(fldName);
                }
                else if (item.IR->name.substr(0, 12) != "l_ainterface")
                    generateModuleSignature(OStr, item.IR, fldName + MODULE_SEPARATOR);
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
            return nullptr; });
    // generate 'assign' items
    for (auto item: outList)
        if (item.second) {
            if (assignList[item.first] != "")
                fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), assignList[item.first].c_str());
            else if (!seenList[item.first])
                fprintf(OStr, "    // assign %s = MISSING_ASSIGNMENT_FOR_OUTPUT_VALUE;\n", item.first.c_str());
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

std::string getRdyName(std::string basename)
{
    std::string rdyName = basename;
    if (endswith(rdyName, "__ENA"))
        rdyName = rdyName.substr(0, rdyName.length()-5);
    rdyName += "__RDY";
    return rdyName;
}

static std::string encapExpr(std::string arg)
{
    std::string temp = arg;
    int ind = temp.find(" ");
    if (ind != -1)
        temp = "(" + temp + ")";
    return temp;
}
static std::string invertExpr(std::string arg)
{
    if (endswith(arg, " ^ 1"))
        return arg.substr(0, arg.length()-4);
    int indparen = arg.find("(");
    int indeq = arg.find("==");
    if (indparen == -1 && indeq > 0)
        return encapExpr(arg.substr(0, indeq) + "!=" + arg.substr(indeq + 2));
    return encapExpr(encapExpr(arg) + " ^ 1");
}

// lift guards from called method interfaces
void promoteGuards(ModuleIR *IR)
{
    for (auto FI : IR->method) {
        std::string methodName = FI.first, rdyName = getRdyName(methodName);
        if (endswith(methodName, "__RDY"))
            continue;
        MethodInfo *MI = IR->method[methodName];
        MethodInfo *MIRdy = IR->method[rdyName];
        assert(MIRdy);
        for (auto info: MI->callList) {
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string calledName = getRdyName(rval.substr(0, ind));
            std::string tempCond;
            if (info.cond != "")
                tempCond = calledName + " | " + invertExpr(info.cond);
            else
                tempCond = calledName;
            rval = cleanupValue(rval.substr(ind+1, rval.length() - 1 - (ind+1)));
            if (MIRdy->guard == "1")
                MIRdy->guard = tempCond;
            else
                MIRdy->guard = encapExpr(MIRdy->guard) + " & " + encapExpr(tempCond);
        }
    }
}
