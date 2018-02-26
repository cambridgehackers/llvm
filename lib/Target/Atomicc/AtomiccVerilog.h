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

typedef struct {
    std::string value;
    bool        valid;
} AssignData;
typedef struct {
    std::string type;
    bool        used;
} WireData;
typedef struct {
    std::string value;
    bool        out;
} ModData;
typedef struct {
    std::string cond;
    std::string value;
} MuxValueEntry;

static std::map<std::string, bool> inList, outList;
static std::map<std::string, AssignData> assignList;
static std::map<std::string, WireData> wireList; // name -> type
static std::list<ModData> modLine;

typedef ModuleIR *(^CBFun)(FieldElement &item, std::string fldName);
#define CBAct ^ ModuleIR * (FieldElement &item, std::string fldName)

bool isIdChar(char ch)
{
    return isalpha(ch) || ch == '_' || ch == '$';
}

std::list<std::string> tokenList;
static void str2token(std::string arg)
{
    int total = arg.length();
    int index = 0;
    char ch = arg[index++];
    tokenList.clear();
    while(index <= total) {
        std::string token;
        auto getNext = [&] (void) -> void {
            token += ch;
            ch = arg[index++];
        };

        if (ch == ' ' || ch == '\t') {
            ch = arg[index++];
        }
        else if (isIdChar(ch)) {
            do {
                getNext();
            } while (isIdChar(ch) || isdigit(ch));
//printf("[%s:%d] token %s\n", __FUNCTION__, __LINE__, token.c_str());
            tokenList.push_back(token);
        }
        else if (isdigit(ch)) {
            do {
                getNext();
            } while (isdigit(ch) || ch == '.');
            tokenList.push_back(token);
        }
        else if (ch == '{') {
            getNext();
            tokenList.push_back(token);
        }
        else if (ch == '+' || ch == '-' || ch == '*' || ch == '&' || ch == '|') {
            do {
                getNext();
            } while (ch == token[0]);
            tokenList.push_back(token);
        }
        else if (ch == '=' || ch == '<' || ch == '>') {
            do {
                getNext();
            } while (ch == '=' || ch == '<' || ch == '>');
            tokenList.push_back(token);
        }
        else if (ch == '/' || ch == '%'
            || ch == '}' || ch == '(' || ch == ')' || ch == '^' || ch == '!'
            || ch == ',' || ch == '?' || ch == ':') {
            getNext();
            tokenList.push_back(token);
        }
        else {
printf("[%s:%d] arg '%s' unknown ch %c\n", __FUNCTION__, __LINE__, arg.c_str(), ch);
            exit(-1);
        }
    }
}

static std::string token2str(std::list<std::string> &argList)
{
    std::string ret, sep;
    for (auto tok: argList) {
        ret += sep + tok;
        sep = " ";
    }
    return ret;
}

static void setAssign(std::string target, std::string value)
{
//printf("[%s:%d] [%s] = %s\n", __FUNCTION__, __LINE__, target.c_str(), value.c_str());
    assignList[target] = AssignData{value, value != ""};
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

static ModuleIR *iterInterface(ModuleIR *IR, CBFun cbWorker)
{
    for (auto item: IR->interfaces) {
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
    bool lookInterface = false;
    while (1) {
        int ind = searchStr.find(MODULE_SEPARATOR);
        std::string tname = searchStr.substr(0, ind);
        if (lookInterface) {
        if (auto nextIR = iterInterface(searchIR, CBAct {
              if (ind != -1 && fldName == tname)
                  return lookupIR(item.type);
              return nullptr; })) {
            searchIR = nextIR;
            goto next;
            }
        }
        else {
        if (auto nextIR = iterField(searchIR, CBAct {
              if (ind != -1 && fldName == tname)
                  return lookupIR(item.type);
              return nullptr; })) {
            searchIR = nextIR;
            goto next;
            }
        }
        {
            for (auto item: searchIR->outcall)
                if (item.fldName == tname) {
                    searchIR = lookupIR(item.type);
                    goto next;
                }
            return searchIR->method[searchStr];
        }
next:
        lookInterface = !lookInterface;
        searchStr = searchStr.substr(ind+1);
    };
}

static void generateModuleSignatureList(ModuleIR *IR, std::string instance)
{
    // First handle all 'incoming' interface methods
    for (auto item : IR->interfaces)
        for (auto FI: lookupIR(item.type)->method) {
            MethodInfo *MI = FI.second;
            if (!MI->rule || instance == "")
                setDir(instance + item.fldName + MODULE_SEPARATOR + FI.first, instance != "", MI); // if !instance, !action -> out
        }
    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    for (auto oitem: IR->outcall)
        for (auto FI : lookupIR(oitem.type)->method) {
            MethodInfo *MI = FI.second;
            if (!MI->rule)
                setDir(oitem.fldName + MODULE_SEPARATOR + FI.first, instance == "", MI); // action -> out
        }

}

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(ModuleIR *IR, std::string instance)
{
    std::string inp = "input ", outp = "output ", inpClk = "input ";
    auto checkWire = [&](std::string wparam, std::string atype, std::string dir, bool out) -> void {
        std::string ret = inp + wparam;
        if (instance != "")
            wireList[ret] = WireData{atype, false};
        else if (atype != "") // !action
            ret = dir + sizeProcess(atype) + wparam;
        modLine.push_back(ModData{ret, out});
    };
    auto sizeT = [&](std::string atype) -> std::string {
        if (instance == "")
            return sizeProcess(atype);
        return "";
    };
//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, IR->name.c_str(), instance.c_str());
    modLine.push_back(ModData{IR->name + " " + ((instance != "") ? instance + " ":"") + "(", false});
    if (instance != "") {
        inp = instance + MODULE_SEPARATOR;
        outp = instance + MODULE_SEPARATOR;
        inpClk = "";
    }
    modLine.push_back(ModData{inpClk + "CLK", false});
    modLine.push_back(ModData{inpClk + "nRST", false});
    // First handle all 'incoming' interface methods
    for (auto item : IR->interfaces)
        for (auto FI: lookupIR(item.type)->method) {
            std::string methodName = item.fldName + MODULE_SEPARATOR + FI.first;
            MethodInfo *MI = FI.second;
            checkWire(methodName, MI->type, outp, true);
            for (auto item: MI->params)
                checkWire(methodName.substr(0, methodName.length()-5) + MODULE_SEPARATOR + item.name, item.type, inp, true);
        }
    // Now handle 'outcalled' interfaces (class members that are pointers to interfaces)
    for (auto oitem: IR->outcall)
        for (auto FI : lookupIR(oitem.type)->method) {
            MethodInfo *MI = FI.second;
            std::string wparam = oitem.fldName + MODULE_SEPARATOR + FI.first;
            modLine.push_back(ModData{(MI->type == ""/* action */ ? outp : inp + sizeT(MI->type)) + wparam, true});
            wparam = wparam.substr(0, wparam.length()-5) + MODULE_SEPARATOR;
            for (auto item: MI->params)
                modLine.push_back(ModData{outp + sizeT(item.type) + wparam + item.name, true});
        }
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
    auto lookupString = [&] (std::string arg) -> std::string {
        str2token(arg);
        std::list<std::string> tokNew;
        for (auto item: tokenList) {
            if (isIdChar(item[0]))
            for (auto aitem: assignList)
                if (aitem.second.value == item) {
                    assignList[aitem.first].valid = false;
                    item = aitem.first;
                    break;
                }
                else if (aitem.first == item && aitem.second.value != "") {
                    assignList[aitem.first].valid = false;
                    item = aitem.second.value;
                    break;
                }
            tokNew.push_back(item);
        }
        std::string ret = token2str(tokNew);
        return ret;
    };

    assignList.clear();
    inList.clear();
    outList.clear();
    wireList.clear();
    modLine.clear();
    generateModuleSignatureList(IR, "");
    iterField(IR, CBAct {
            if (ModuleIR *itemIR = lookupIR(item.type))
            if (!item.isPtr && itemIR->name.substr(0,12) != "l_struct_OC_")
                generateModuleSignatureList(itemIR, fldName + MODULE_SEPARATOR);
          return nullptr;
          });

    // Generate module header
    generateModuleSignature(IR, "");
    std::string sep = "module ";
    for (auto mitem: modLine) {
        fprintf(OStr, "%s", (sep + mitem.value).c_str());
        if (mitem.value[mitem.value.length()-1] == '(')
            sep = "\n    ";
        else
            sep = ",\n    ";
    }
    fprintf(OStr, ");\n");
    modLine.clear();
    for (auto item: IR->softwareName)
        fprintf(OStr, "// software: %s\n", item.c_str());
    for (auto IC : IR->interfaceConnect)
        for (auto FI : lookupIR(IC.type)->method) {
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
        MethodInfo *MI = FI.second;
        for (auto item: MI->alloca)
            fprintf(OStr, "    wire %s;\n", (sizeProcess(item.second) + item.first).c_str());
        bool alwaysSeen = false;
        for (auto info: MI->letList)
            muxValueList[info.dest].push_back(MuxValueEntry{info.cond, cleanupValue(info.value)});
        for (auto info: MI->storeList) {
            if (!alwaysSeen)
                alwaysLines.push_back("if (" + methodName + ") begin");
            alwaysSeen = true;
            if (info.cond != "")
                alwaysLines.push_back("    if (" + info.cond + ")");
            alwaysLines.push_back("    " + info.dest + " <= " + cleanupValue(info.value) + ";");
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
            int argCount = CI->params.size();
            while(rval.length() && argCount-- > 0) {
                std::string rest;
                std::string scanexp = scanExpression(rval.c_str());
                rest = rval.substr(scanexp.length());
                while (rest[0] == ' ')
                    rest = rest.substr(1);
                if (rest.length()) {
                    if (rest[0] == ',')
                        rest = rest.substr(1);
                    else
                        printf("[%s:%d] cannot locate ','\n", __FUNCTION__, __LINE__);
                }
                muxValueList[pname + AI->name].push_back(MuxValueEntry{tempCond, scanexp});
                rval = rest;
                AI++;
            }
            if (rval.length()) {
printf("[%s:%d] unused arguments '%s' from '%s'\n", __FUNCTION__, __LINE__, rval.c_str(), info.value.c_str());
                exit(-1);
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
    for (auto FI : IR->method)
        setAssign(FI.first, FI.second->guard);  // collect the text of the return value into a single 'assign'
    // generate local state element declarations
    iterField(IR, CBAct {
            uint64_t size = convertType(item.type);
            ModuleIR *itemIR = lookupIR(item.type);
            if (itemIR && !item.isPtr) {
                if (itemIR->name.substr(0,12) == "l_struct_OC_") {
                    fprintf(OStr, "    reg%s;\n", (sizeProcess(item.type) + " " + fldName).c_str());
                    resetList.push_back(fldName);
                }
                else
                    generateModuleSignature(itemIR, fldName);
            }
            else if (size != 0) {
                std::string temp;
                if (size > 8)
                    temp += "[" + autostr(size - 1) + ":0]";
                temp += " " + fldName;
                if (item.arrayLen > 0)
                    temp += "[" + autostr(item.arrayLen) + ":0]";
                fprintf(OStr, "    reg%s;\n", temp.c_str());
                resetList.push_back(fldName);
            }
            return nullptr; });
    // now write actual module signature to output file
    std::list<std::string> modNew;
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto outerItem: assignList)
            for (auto aitem: assignList)
                if (aitem.first == outerItem.second.value && aitem.second.value != "") {
                    assignList[aitem.first].valid = false;
                    assignList[outerItem.first].value = aitem.second.value;
                    changed = true;
                    break;
                }
    }
    for (auto mitem: modLine)
        modNew.push_back(lookupString(mitem.value));
    for (auto mitem: modNew) {
        str2token(mitem);
        for (auto item: tokenList)
            if (isIdChar(item[0]))
                wireList[item].used = true;
    }
    for (auto aitem: assignList) {
        if (aitem.second.value != "" && aitem.second.valid) {
        str2token(aitem.second.value);
        wireList[aitem.first].used = true;
        for (auto item: tokenList)
            if (isIdChar(item[0]))
                wireList[item].used = true;
        }
    }
    for (auto item: wireList)
        if (item.second.type != "" && item.second.used)
        fprintf(OStr, "    wire %s;\n", (sizeProcess(item.second.type) + item.first).c_str());
    std::string endStr;
    for (auto item: modNew) {
        if (item[item.length()-1] == '(') {
            fprintf(OStr, "%s", (endStr + "    " + item).c_str());
            sep = "";
        }
        else {
            fprintf(OStr, "%s", (sep + "\n        " + item).c_str());
            sep = ",";
        }
        endStr = ");\n";
    }
    fprintf(OStr, "%s", endStr.c_str());
    // generate 'assign' items
    for (auto item: outList)
        if (item.second) {
            if (assignList[item.first].value == "")
                fprintf(OStr, "    // assign %s = MISSING_ASSIGNMENT_FOR_OUTPUT_VALUE;\n", item.first.c_str());
            else if (assignList[item.first].valid)
                fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), assignList[item.first].value.c_str());
            assignList[item.first].valid = false;
        }
    bool seen = false;
    for (auto item: assignList)
        if (item.second.valid) {
            if (!seen)
                fprintf(OStr, "    // Extra assigments, not to output wires\n");
            seen = true;
            fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), item.second.value.c_str());
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
        MethodInfo *MI = FI.second;
        MethodInfo *MIRdy = IR->method[rdyName];
        assert(MIRdy);
        for (auto info: MI->callList) {
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string tempCond = getRdyName(rval.substr(0, ind));
            if (info.cond != "")
                tempCond += " | " + invertExpr(info.cond);
            rval = cleanupValue(rval.substr(ind+1, rval.length() - 1 - (ind+1)));
            if (MIRdy->guard == "1")
                MIRdy->guard = tempCond;
            else
                MIRdy->guard = encapExpr(MIRdy->guard) + " & " + encapExpr(tempCond);
        }
    }
}
