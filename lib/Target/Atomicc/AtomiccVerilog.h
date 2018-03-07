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
    std::string value;
    bool        out;
} ModData;
typedef struct {
    std::string cond;
    std::string value;
} MuxValueEntry;
typedef struct {
    std::string name;
    std::string type;
} FieldItem;

static std::list<FieldItem> fieldList;
static std::map<std::string, bool> inList, outList;
static std::map<std::string, AssignData> assignList;
static std::map<std::string, std::string> wireList; // name -> type

typedef ModuleIR *(^CBFun)(FieldElement &item, std::string fldName);
#define CBAct ^ ModuleIR * (FieldElement &item, std::string fldName)

bool isIdChar(char ch)
{
    return isalpha(ch) || ch == '_' || ch == '$';
}

static void str2token(std::string arg, std::list<std::string> &tokenList)
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
        else if (ch == '+' || ch == '-' || ch == '*' || ch == '&' || ch == '|') {
            do {
                getNext();
            } while (ch == token[0]);
            tokenList.push_back(token);
        }
        else if (ch == '=' || ch == '<' || ch == '>' || ch == '!') {
            do {
                getNext();
            } while (ch == '=' || ch == '<' || ch == '>');
            tokenList.push_back(token);
        }
        else if (ch == '/' || ch == '%' || ch == '{'
            || ch == '}' || ch == '(' || ch == ')' || ch == '^'
            || ch == ',' || ch == '?' || ch == ':' || ch == ';') {
            getNext();
            tokenList.push_back(token);
        }
        else {
printf("[%s:%d] arg '%s' unknown ch %c\n", __FUNCTION__, __LINE__, arg.c_str(), ch);
            exit(-1);
        }
    }
}

static void setAssign(std::string target, std::string value)
{
//printf("[%s:%d] [%s] = %s\n", __FUNCTION__, __LINE__, target.c_str(), value.c_str());
    std::string ret, sep;
    std::list<std::string> tokenList;
    str2token(value, tokenList);
    for (auto tok: tokenList) {
        ret += sep + tok;
        sep = " ";
    }
    assignList[target] = AssignData{ret, true};
}

static std::string sizeProcess(std::string type)
{
    uint64_t val = convertType(type);
    if (val > 1)
        return "[" + autostr(val - 1) + ":0]";
    return "";
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
    std::string fieldName;
    while (1) {
        int ind = searchStr.find(MODULE_SEPARATOR);
        fieldName = searchStr.substr(0, ind);
        searchStr = searchStr.substr(ind+1);
        ModuleIR *nextIR = iterField(searchIR, CBAct {
              if (ind != -1 && fldName == fieldName)
                  return lookupIR(item.type);
              return nullptr; });
        if (!nextIR)
            break;
        searchIR = nextIR;
    };
    for (auto item: searchIR->interfaces)
        if (item.fldName == fieldName)
            return lookupIR(item.type)->method[searchStr];
    return NULL;
}

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(ModuleIR *IR, std::string instance, std::list<ModData> &modParam)
{
    std::string prefix[2] = {"input ", "output "};
    std::string inpClk = "input ";
    auto checkWire = [&](std::string wparam, std::string atype, int dir) -> void {
        std::string ret = prefix[1 - dir] + wparam;
        if (instance != "")
            wireList[ret] = atype;
        else if (atype != "") // !action
            ret = prefix[dir] + sizeProcess(atype) + wparam;
        modParam.push_back(ModData{ret, true});
    };
//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, IR->name.c_str(), instance.c_str());
    for (auto item : IR->interfaces)
        for (auto FI: lookupIR(item.type)->method) {
            MethodInfo *MI = FI.second;
            std::string name = instance + item.fldName + MODULE_SEPARATOR + FI.first;
            bool out = (instance != "") ^ item.isPtr;
            auto setItem = [&](std::string extra, bool oo) {
                if (oo)
                    outList[extra] = true;
                else
                    inList[extra] = true;
            };
            if (!MI->rule || instance == "") {
                // if !instance, !action -> out
                setItem(name, out == (MI->type == ""));
                for (auto item: MI->params)
                    setItem(name.substr(0, name.length()-5) + MODULE_SEPARATOR + item.name, out);
            }
        }
    modParam.push_back(ModData{IR->name + " " + ((instance != "") ? instance.substr(0, instance.length()-1) + " ":"") + "(", false});
    if (instance != "") {
        prefix[0] = instance;
        prefix[1] = instance;
        inpClk = "";
    }
    modParam.push_back(ModData{inpClk + "CLK", false});
    modParam.push_back(ModData{inpClk + "nRST", false});
    for (auto item : IR->interfaces)
        for (auto FI: lookupIR(item.type)->method) {
            std::string methodName = item.fldName + MODULE_SEPARATOR + FI.first;
            MethodInfo *MI = FI.second;
            checkWire(methodName, MI->type, 1 - item.isPtr);
            for (auto pitem: MI->params)
                checkWire(methodName.substr(0, methodName.length()-5) + MODULE_SEPARATOR + pitem.name, pitem.type, item.isPtr);
        }
}

static void getFieldList(std::string name, std::string type)
{
    if (ModuleIR *IR = lookupIR(type))
        for (auto item: IR->fields)
            getFieldList(name + MODULE_SEPARATOR + item.fldName, item.type);
    else
        fieldList.push_back(FieldItem{name, type});
}

/*
 * Generate *.v and *.vh for a Verilog module
 */
void generateModuleDef(ModuleIR *IR, FILE *OStr)
{
static std::list<ModData> modLine;
static std::map<std::string, std::string> regList; // why 'static' ?????!!!!!!
    std::map<std::string, std::string> enableList;
    std::map<std::string, bool> refList, refSource;
    // 'Mux' together parameter settings from all invocations of a method from this class
    std::map<std::string, std::list<MuxValueEntry>> muxValueList;
    auto lookupString = [&] (std::string arg, bool setReference) -> std::string {
        std::list<std::string> tokenList;
        str2token(cleanupValue(arg), tokenList);
        std::string ret, sep;
        for (auto item: tokenList) {
            if (isIdChar(item[0])) {
            std::string temp = assignList[item].value;
            if (temp != "") {
                assignList[item].valid = false;
                if (setReference)
                    refSource[item] = true;
                refList[item] = false;
                item = temp;
            }
            if (setReference)
                refList[item] = true;
            }
            ret += sep + item;
            sep = " ";
        }
        return ret;
    };

    assignList.clear();
    inList.clear();
    outList.clear();
    wireList.clear();
    regList.clear();
    modLine.clear();
    generateModuleSignature(IR, "", modLine);
    for (auto item: outList)
        if (item.second)
            refList[item.first] = true;
    // Generate module header
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
    iterField(IR, CBAct {
            ModuleIR *itemIR = lookupIR(item.type);
            if (itemIR && !item.isPtr) {
            if (itemIR->name.substr(0,12) == "l_struct_OC_") {
                fieldList.clear();
                getFieldList(fldName, item.type);
                std::string itemList;
                for (auto fitem : fieldList) {
                    regList[fitem.name] = fitem.type;
                    itemList += " , " + fitem.name;
                }
                setAssign(fldName, "{" + itemList.substr(2) + " }");
            }
            else
                generateModuleSignature(itemIR, fldName + MODULE_SEPARATOR, modLine);
            }
            else if (convertType(item.type) != 0)
                regList[fldName] = item.type;
          return nullptr;
          });

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
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = FI.second;
        if (MI->rule)
            refList[methodName] = true;
        for (auto item: MI->alloca) {
            fieldList.clear();
            getFieldList(item.first, item.second);
            std::string itemList;
            for (auto fitem : fieldList) {
                wireList[fitem.name] = fitem.type;
                itemList += " , " + fitem.name;
            }
            wireList[item.first] = item.second;
            setAssign(item.first, "{" + itemList.substr(2) + " }");
        }
        for (auto info: MI->letList) {
            fieldList.clear();
            getFieldList("", info.type);
            std::string itemList;
            for (auto fitem : fieldList) {
                std::string fname = fitem.name;
                muxValueList[info.dest + fname].push_back(MuxValueEntry{info.cond, info.value + fname});
            }
        }
        for (auto info: MI->callList) {
            if (!info.isAction)
                continue;
            std::string tempCond = methodName;
            if (info.cond != "")
                tempCond += " & " + info.cond;
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string calledName = rval.substr(0, ind);
            rval = rval.substr(ind+1, rval.length() - 1 - (ind+1));
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
                std::string scanexp = scanExpression(rval.c_str());
                std::string rest = rval.substr(scanexp.length());
                while (rest[0] == ' ')
                    rest = rest.substr(1);
                if (rest.length()) {
                    if (rest[0] == ',')
                        rest = rest.substr(1);
                    else
                        printf("[%s:%d] cannot locate ',' in '%s'\n", __FUNCTION__, __LINE__, rest.c_str());
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
            prevCond = cleanupValue(element.cond);
            prevValue = cleanupValue(element.value);
        }
        setAssign(item.first, temp + prevValue);
    }
    for (auto FI : IR->method)
        setAssign(FI.first, FI.second->guard);  // collect the text of the return value into a single 'assign'
    // process all replacements within the list of 'setAssign' items
    bool changed = true;
    while (changed) {
        changed = false;
        for (auto outerItem: assignList) {
            std::string newItem = lookupString(outerItem.second.value, false);
            if (newItem != outerItem.second.value) {
//printf("[%s:%d] change [%s] = %s -> %s\n", __FUNCTION__, __LINE__, outerItem.first.c_str(), outerItem.second.value.c_str(), newItem.c_str());
                assignList[outerItem.first].value = newItem;
                changed = true;
            }
        }
    }

    // generate local state element declarations
    for (auto item: regList)
        fprintf(OStr, "    reg%s;\n", (sizeProcess(item.second) + " " + item.first).c_str());
    // now write actual module signature to output file
    std::list<std::string> modNew;
    for (auto mitem: modLine)
        modNew.push_back(lookupString(mitem.value, true));
    std::list<std::string> alwaysLines;
    for (auto FI : IR->method) {
        bool alwaysSeen = false;
        for (auto info: FI.second->storeList) {
            if (!alwaysSeen)
                alwaysLines.push_back("if (" + FI.first + ") begin");
            alwaysSeen = true;
            if (info.cond != "")
                alwaysLines.push_back("    if (" + lookupString(info.cond, true) + ")");
            alwaysLines.push_back("    " + info.dest + " <= " + lookupString(info.value, true) + ";");
        }
        if (alwaysSeen)
            alwaysLines.push_back("end; // End of " + FI.first);
    }
    // Now calculated 'was referenced' from assignList items actually referenced
    changed = true;
    std::map<std::string, bool> excludeList;
    while (changed) {
        changed = false;
        for (auto aitem: assignList) {
            if (aitem.second.value != "" && (refList[aitem.first] || refSource[aitem.first])
              && !excludeList[aitem.first]) {
                excludeList[aitem.first] = true;
                std::list<std::string> tokenList;
                str2token(aitem.second.value, tokenList);
                for (auto item: tokenList)
                    if (isIdChar(item[0]))
                        refList[item] = true;
                changed = true;
            }
        }
    }
    for (auto aitem: assignList) {
if (aitem.second.value != "")
printf("[%s:%d] ASSIGN %s = %s %d\n", __FUNCTION__, __LINE__, aitem.first.c_str(), aitem.second.value.c_str(), aitem.second.valid);
    }
    for (auto item: wireList)
        if (refList[item.first] && item.second != "")
            fprintf(OStr, "    wire %s;\n", (sizeProcess(item.second) + item.first).c_str());
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
            else if (assignList[item.first].valid && refList[item.first])
                fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), assignList[item.first].value.c_str());
            refList[item.first] = false;
        }
    bool seen = false;
    for (auto item: assignList)
        if (item.second.value != "" && item.second.valid && refList[item.first]) {
            if (!seen)
                fprintf(OStr, "    // Extra assigments, not to output wires\n");
            seen = true;
            fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), item.second.value.c_str());
        }
    // generate clocked updates to state elements
    if (regList.size() > 0 || alwaysLines.size() > 0) {
        fprintf(OStr, "\n    always @( posedge CLK) begin\n      if (!nRST) begin\n");
        for (auto item: regList)
            fprintf(OStr, "        %s <= 0;\n", item.first.c_str());
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
