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
    std::string type;
    bool        moduleStart;
    int         out;
} ModData;
typedef struct {
    ACCExpr    *cond;
    ACCExpr    *value;
} MuxValueEntry;
typedef struct {
    std::string name;
    std::string type;
    bool        alias;
    uint64_t    offset;
} FieldItem;
typedef struct {
    ACCExpr    *value;
    std::string type;
} AssignItem;
static int trace_assign;//= 1;

static std::map<std::string, bool> inList, outList, refList;
static std::map<std::string, AssignItem> assignList;
static std::map<std::string, std::string> typeList, regList, wireList; // name -> type

typedef ModuleIR *(^CBFun)(FieldElement &item, std::string fldName);
#define CBAct ^ ModuleIR * (FieldElement &item, std::string fldName)

static void setAssign(std::string target, ACCExpr *value, std::string type)
{
if (trace_assign && value) printf("[%s:%d] start [%s] = %s type '%s'\n", __FUNCTION__, __LINE__, target.c_str(), tree2str(value).c_str(), type.c_str());
    assignList[target] = AssignItem{value, type};
}

static ModuleIR *lookupIR(std::string ind)
{
    if (ind == "")
        return nullptr;
    ModuleIR *ret = mapIndex[ind];
    //ParseCheck(ret != NULL, "lookupIR = " + ind + " not found");
    return ret;
}

static uint64_t convertType(std::string arg)
{
    if (arg == "" || arg == "void")
        return 0;
    const char *bp = arg.c_str();
    auto checkT = [&] (const char *val) -> bool {
        int len = strlen(val);
        bool ret = !strncmp(bp, val, len);
        if (ret)
            bp += len;
        return ret;
    };
    if (checkT("INTEGER_"))
        return atoi(bp);
    if (checkT("ARRAY_"))
        return convertType(bp);
    if (auto IR = lookupIR(bp)) {
        uint64_t total = 0;
        for (auto item: IR->fields)
            total += convertType(item.type);
        return total;
    }
    printf("[%s:%d] convertType FAILED '%s'\n", __FUNCTION__, __LINE__, bp);
    exit(-1);
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

static void getFieldList(std::list<FieldItem> &fieldList, std::string name, std::string type, bool force = true, uint64_t offset = 0, bool alias = false, bool init = true)
{
    if (init)
        fieldList.clear();
    if (ModuleIR *IR = lookupIR(type)) {
        if (IR->unionList.size() > 0) {
            for (auto item: IR->unionList)
                getFieldList(fieldList, name + MODULE_SEPARATOR + item.name, item.type, true, offset, true, false);
            for (auto item: IR->fields) {
                fieldList.push_back(FieldItem{name, item.type, false, offset}); // aggregate data
                offset += convertType(item.type);
            }
        }
        else
            for (auto item: IR->fields) {
                getFieldList(fieldList, name + MODULE_SEPARATOR + item.fldName, item.type, true, offset, alias, false);
                offset += convertType(item.type);
            }
    }
    else if (force)
        fieldList.push_back(FieldItem{name, type, alias, offset});
}

static void expandStruct(ModuleIR *IR, std::string fldName, std::string type,
     std::map<std::string, std::string> &declList, int out, bool force)
{
    std::string itemList;
    std::list<FieldItem> fieldList;
    getFieldList(fieldList, fldName, type, force);
    for (auto fitem : fieldList) {
        declList[fitem.name] = fitem.type;
printf("[%s:%d] set %s = %s\n", __FUNCTION__, __LINE__, fitem.name.c_str(), fitem.type.c_str());
        uint64_t offset = fitem.offset;
        uint64_t upper = offset + convertType(fitem.type) - 1;
        if (fitem.alias) {
            setAssign(fitem.name, allocExpr(fldName + "[" + autostr(offset) + ":" + autostr(upper) + "]"), fitem.type);
            typeList[fitem.name] = fitem.type;
        }
        else if (out)
            itemList += " , " + fitem.name;
        else
            setAssign(fitem.name, allocExpr(fldName + "[" + autostr(offset) + ":" + autostr(upper) + "]"), fitem.type);
    }
    if (itemList.length() > 2)
    setAssign(fldName, str2tree("{" + itemList.substr(2) + " }"), type);
}

static void walkRef (ACCExpr *expr)
{
    std::string item = expr->value;
    if (isIdChar(item[0]))
        refList[item] = true;
    for (auto item: expr->operands)
        walkRef(item);
    if (expr->next)
        walkRef(expr->next);
}
static std::string walkTree (ACCExpr *expr, bool *changed)
{
    std::string ret = expr->value;
    if (isIdChar(ret[0])) {
if (trace_assign)
printf("[%s:%d] check '%s' exprtree %p\n", __FUNCTION__, __LINE__, ret.c_str(), assignList[ret].value);
        if (ACCExpr *temp = assignList[ret].value) {
            refList[ret] = false;
if (trace_assign)
printf("[%s:%d] changed %s -> %s\n", __FUNCTION__, __LINE__, ret.c_str(), tree2str(temp).c_str());
            ret = walkTree(temp, changed);
            if (changed)
                *changed = true;
            else
                walkRef(temp);
        }
        else if (!changed)
            refList[ret] = true;
    }
    else {
        ret = "";
        std::string sep, op = expr->value;
        if (isParenChar(op[0])) {
            ret += op + " ";
            op = "";
        }
        if (!expr->operands.size())
            ret += op;
        for (auto item: expr->operands) {
            ret += sep + walkTree(item, changed);
            sep = " " + op + " ";
            if (op == "?")
                op = ":";
        }
    }
    ret += treePost(expr);
    if (expr->next)
        ret += " " + walkTree(expr->next, changed);
    return ret;
}

std::string findType(std::string name)
{
    ACCExpr *expr = str2tree(name);
    if (expr->value == "(" && expr->next) {
        expr = expr->next;
        if (expr->value == "?" && expr->next)
            expr = expr->next;
    }
    else if (expr->value == "?") {
        int i = 0;
        for (auto item: expr->operands)
            if (i++ == 1) {
                expr = item;
                break;
            }
    }
//printf("[%s:%d] name %s expr %s\n", __FUNCTION__, __LINE__, name.c_str(), expr->value.c_str());
    if (regList.find(expr->value) != regList.end())
        return regList[expr->value];
    else if (typeList.find(expr->value) != typeList.end())
        return typeList[expr->value];
    else if (wireList.find(expr->value) != wireList.end())
        return wireList[expr->value];
    else if (assignList.find(expr->value) != assignList.end())
        return assignList[expr->value].type;
printf("[%s:%d] reference to '%s', but could not locate RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRRR \n", __FUNCTION__, __LINE__, name.c_str());
    //exit(-1);
    return "";
}
/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(ModuleIR *IR, std::string instance, std::list<ModData> &modParam,
    std::map<std::string, std::string> &wireList)
{
    auto checkWire = [&](std::string name, std::string type, int dir) -> void {
        if (dir)
            outList[name] = true;
        else
            inList[name] = true;
        if (type == "")
            type = "void";
        typeList[name] = type;
        modParam.push_back(ModData{name, type, false, dir});
    };
//printf("[%s:%d] name %s instance %s\n", __FUNCTION__, __LINE__, IR->name.c_str(), instance.c_str());
    modParam.push_back(ModData{IR->name + ((instance != "") ? " " + instance.substr(0, instance.length()-1):""), "", true, 0});
    for (auto item : IR->interfaces)
        for (auto FI: lookupIR(item.type)->method) {
            MethodInfo *MI = FI.second;
            std::string name = instance + item.fldName + MODULE_SEPARATOR + FI.first;
            bool out = (instance != "") ^ item.isPtr;
            checkWire(name, MI->type, out ^ (MI->type != ""));
            for (auto pitem: MI->params)
                checkWire(name.substr(0, name.length()-5) + MODULE_SEPARATOR + pitem.name, pitem.type, out);
        }
}

/*
 * Generate *.v and *.vh for a Verilog module
 */
void generateModuleDef(ModuleIR *IR, FILE *OStr)
{
static std::list<ModData> modLine;
    std::map<std::string, std::string> enableList;
    refList.clear();
    // 'Mux' together parameter settings from all invocations of a method from this class
    std::map<std::string, std::list<MuxValueEntry>> muxValueList;

    assignList.clear();
    typeList.clear();
    inList.clear();
    outList.clear();
    wireList.clear();
    regList.clear();
    modLine.clear();
    generateModuleSignature(IR, "", modLine, wireList);
    for (auto item: outList)
        if (item.second)
            refList[item.first] = true;
    // Generate module header
    std::string sep = "module ";
    for (auto mitem: modLine) {
        static const char *dirStr[] = {"input", "output"};
        fprintf(OStr, "%s", sep.c_str());
        if (mitem.moduleStart)
            fprintf(OStr, "%s (\n    input CLK,\n    input nRST", mitem.value.c_str());
        else {
            fprintf(OStr, "%s %s%s", dirStr[mitem.out], sizeProcess(mitem.type).c_str(), mitem.value.c_str());
            //expandStruct(IR, mitem.value, mitem.type, wireList, mitem.out, false);
        }
        sep = ",\n    ";
    }
    fprintf(OStr, ");\n");
    modLine.clear();
    for (auto item: IR->softwareName)
        fprintf(OStr, "// software: %s\n", item.c_str());
    iterField(IR, CBAct {
            ModuleIR *itemIR = lookupIR(item.type);
            if (itemIR && !item.isPtr) {
            if (startswith(itemIR->name, "l_struct_OC_"))
{
printf("[%s:%d] BBBBBBBBBBBBBBBBBBBBBBBBBBBBB %s type %s\n", __FUNCTION__, __LINE__, fldName.c_str(), item.type.c_str());
                expandStruct(IR, fldName, item.type, regList, 1, true);
}
            else
                generateModuleSignature(itemIR, fldName + MODULE_SEPARATOR, modLine, wireList);
            }
            else if (convertType(item.type) != 0)
                regList[fldName] = item.type;
          return nullptr;
          });
    for (auto mitem: modLine)
        if (!mitem.moduleStart) {
            wireList[mitem.value] = mitem.type;
            //expandStruct(IR, mitem.value, mitem.type, wireList, 0/*mitem.out*/, false);
        }

    for (auto IC : IR->interfaceConnect)
        for (auto FI : lookupIR(IC.type)->method) {
            std::string tstr = IC.target + MODULE_SEPARATOR + FI.first,
                        sstr = IC.source + MODULE_SEPARATOR + FI.first;
//printf("[%s:%d] IFCCC %s/%d %s/%d\n", __FUNCTION__, __LINE__, tstr.c_str(), outList[tstr], sstr.c_str(), outList[sstr]);
            if (outList[sstr])
                setAssign(sstr, allocExpr(tstr), FI.second->type);
            else
                setAssign(tstr, allocExpr(sstr), FI.second->type);
            tstr = tstr.substr(0, tstr.length()-5) + MODULE_SEPARATOR;
            sstr = sstr.substr(0, sstr.length()-5) + MODULE_SEPARATOR;
            for (auto info: FI.second->params)
                setAssign(sstr + info.name, allocExpr(tstr + info.name), info.type);
        }
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = FI.second;
        setAssign(methodName, MI->guard, MI->type);  // collect the text of the return value into a single 'assign'
        if (MI->rule) {
            refList[methodName] = true;
            std::string type = MI->type;
            if (type == "")
                type = "void";
            typeList[methodName] = type;
        }
        for (auto item: MI->alloca)
            expandStruct(IR, item.first, item.second, wireList, 1, true);
        for (auto info: MI->letList) {
            std::list<FieldItem> fieldList;
            getFieldList(fieldList, "", info.type, true);
            for (auto fitem : fieldList) {
                std::string dest = tree2str(info.dest) + fitem.name;
                std::string src = tree2str(info.value) + fitem.name;
                typeList[dest] = fitem.type;
                typeList[src] = fitem.type;
                muxValueList[dest].push_back(MuxValueEntry{info.cond, str2tree(src)});
            }
        }
        for (auto info: MI->callList) {
            if (!info.isAction)
                continue;
            ACCExpr *tempCond = str2tree(methodName);
            if (info.cond) {
                appendExpr(tempCond, allocExpr("&"));
                appendExpr(tempCond, info.cond);
            }
            std::string calledName = info.value->value;
printf("[%s:%d] CALLLLLL '%s'\n", __FUNCTION__, __LINE__, calledName.c_str());
            if (!info.value->operands.size() || info.value->operands.front()->value != "{") {
                printf("[%s:%d] incorrectly formed call expression\n", __FUNCTION__, __LINE__);
                exit(-1);
            }
            // 'Or' together ENA lines from all invocations of a method from this class
            if (info.isAction)
                enableList[calledName] += " || " + tree2str(tempCond);
            MethodInfo *CI = lookupQualName(IR, calledName);
            if (!CI) {
                printf("[%s:%d] method %s not found\n", __FUNCTION__, __LINE__, calledName.c_str());
                exit(-1);
            }
            auto AI = CI->params.begin();
            std::string pname = calledName.substr(0, calledName.length()-5) + MODULE_SEPARATOR;
            int argCount = CI->params.size();
            ACCExpr *param = info.value->operands.front()->operands.front();
printf("[%s:%d] param '%s'\n", __FUNCTION__, __LINE__, tree2str(param).c_str());
//dumpExpr("param", param);
if (param && param->value == ",") {
for (auto item: param->operands) {
            if(argCount-- > 0) {
                std::string scanexp = tree2str(item);
printf("[%s:%d] infmuxVL[%s] = cond '%s' tree '%s'\n", __FUNCTION__, __LINE__, (pname + AI->name).c_str(),
tree2str(tempCond).c_str(), scanexp.c_str());
                muxValueList[pname + AI->name].push_back(MuxValueEntry{tempCond, str2tree(scanexp)});
                typeList[pname + AI->name] = AI->type;
                AI++;
            }
}
}
else {
            while(param && argCount-- > 0) {
                std::string scanexp, sep;
                while(param && param->value != ",") {
                    if (param->value != "{") {
                        scanexp += sep + param->value;
                        for (auto item: param->operands)
                            scanexp += " " + tree2str(item);
                        scanexp += treePost(param);
                        sep = " ";
                    }
                    param = param->next;
                }
                if (param)
                    param = param->next;
printf("[%s:%d] muxVL[%s] = cond '%s' tree '%s'\n", __FUNCTION__, __LINE__, (pname + AI->name).c_str(),
tree2str(tempCond).c_str(), scanexp.c_str());
                muxValueList[pname + AI->name].push_back(MuxValueEntry{tempCond, str2tree(scanexp)});
                typeList[pname + AI->name] = AI->type;
                AI++;
            }
            if (param) {
printf("[%s:%d] unused arguments '%s' from '%s'\n", __FUNCTION__, __LINE__, tree2str(param).c_str(), tree2str(info.value).c_str());
                exit(-1);
            }
}
        }
    }
    for (auto item: enableList)
        setAssign(item.first, str2tree(item.second.substr(4)) /* remove leading '||'*/, "INTEGER_1");
    // combine mux'ed assignments into a single 'assign' statement
    // Context: before local state declarations, to allow inlining
    for (auto item: muxValueList) {
        std::string prevCond;
        std::string temp, prevValue;
        for (auto element: item.second) {
            if (prevCond != "")
                temp += prevCond + " ? " + prevValue + " : ";
            prevCond = tree2str(element.cond);
            prevValue = tree2str(element.value);
        }
        setAssign(item.first, str2tree(temp + prevValue), typeList[item.first]);
    }
    // recursively process all replacements internal to the list of 'setAssign' items
    for (auto item: assignList)
        if (item.second.value) {
if (trace_assign)
printf("[%s:%d] checking [%s] = '%s'\n", __FUNCTION__, __LINE__, item.first.c_str(), tree2str(item.second.value).c_str());
            bool treeChanged = false;
            std::string newItem = walkTree(item.second.value, &treeChanged);
            if (treeChanged) {
if (trace_assign)
printf("[%s:%d] change [%s] = %s -> %s\n", __FUNCTION__, __LINE__, item.first.c_str(), tree2str(item.second.value).c_str(), newItem.c_str());
                assignList[item.first].value = str2tree(newItem);
            }
        }

    // process assignList replacements, mark referenced items
    std::list<ModData> modNew;
    for (auto mitem: modLine) {
        std::string val = mitem.value;
        if (!mitem.moduleStart)
            val = walkTree(str2tree(mitem.value), nullptr);
        modNew.push_back(ModData{val, mitem.type, mitem.moduleStart, mitem.out});
    }
    std::list<std::string> alwaysLines;
    bool hasAlways = false;
    for (auto FI : IR->method) {
        bool alwaysSeen = false;
        for (auto info: FI.second->storeList) {
std::string dest = tree2str(info.dest);
std::string destType = findType(dest);
if (destType == "") {
printf("[%s:%d] typenotfound %s\n", __FUNCTION__, __LINE__, dest.c_str());
exit(-1);
}
            hasAlways = true;
            if (!alwaysSeen)
                alwaysLines.push_back("if (" + FI.first + ") begin");
            alwaysSeen = true;
            if (info.cond)
                alwaysLines.push_back("    if (" + walkTree(info.cond, nullptr) + ")");
            alwaysLines.push_back("    " + tree2str(info.dest) + " <= " + walkTree(info.value, nullptr) + ";");
        }
        if (alwaysSeen)
            alwaysLines.push_back("end; // End of " + FI.first);
    }

    // Now extend 'was referenced' from assignList items actually referenced
    for (auto aitem: assignList)
        if (aitem.second.value && refList[aitem.first])
            walkRef(aitem.second.value);
    if (trace_assign)
    for (auto aitem: assignList)
        if (aitem.second.value)
            printf("[%s:%d] ASSIGN %s = %s\n", __FUNCTION__, __LINE__, aitem.first.c_str(), tree2str(aitem.second.value).c_str());
    for (auto item: refList)
        if (item.second) {
         std::string type = findType(item.first);
        }

    // generate local state element declarations and wires
    for (auto item: regList) {
        hasAlways = true;
        fprintf(OStr, "    reg %s;\n", (sizeProcess(item.second) + item.first).c_str());
    }
    for (auto item: wireList)
        if (refList[item.first])
            fprintf(OStr, "    wire %s;\n", (sizeProcess(item.second) + item.first).c_str());
    std::string endStr;
    for (auto item: modNew) {
        if (item.moduleStart) {
            fprintf(OStr, "%s (\n        CLK,\n        nRST,", (endStr + "    " + item.value).c_str());
            sep = "";
        }
        else {
            fprintf(OStr, "%s", (sep + "\n        " + item.value).c_str());
            sep = ",";
        }
        endStr = ");\n";
    }
    fprintf(OStr, "%s", endStr.c_str());

    // generate 'assign' items
    for (auto item: outList)
        if (item.second) {
            if (!assignList[item.first].value)
                fprintf(OStr, "    // assign %s = MISSING_ASSIGNMENT_FOR_OUTPUT_VALUE;\n", item.first.c_str());
            else if (refList[item.first])
                fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), tree2str(assignList[item.first].value).c_str());
            refList[item.first] = false;
        }
    bool seen = false;
    for (auto item: assignList)
        if (item.second.value && refList[item.first]) {
            if (!seen)
                fprintf(OStr, "    // Extra assigments, not to output wires\n");
            seen = true;
            fprintf(OStr, "    assign %s = %s;\n", item.first.c_str(), tree2str(item.second.value).c_str());
        }
    // generate clocked updates to state elements
    if (hasAlways) {
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

static std::string invertExpr(ACCExpr *expr)
{
    std::string arg = tree2str(expr);
    if (endswith(arg, " ^ 1"))
        return arg.substr(0, arg.length()-4);
    int indparen = arg.find("(");
    int indeq = arg.find("==");
    if (indparen == -1 && indeq > 0)
        return "(" + arg.substr(0, indeq) + "!=" + arg.substr(indeq + 2) + ")";
    return "((" + arg + ") ^ 1)";
}

// lift guards from called method interfaces
void promoteGuards(ModuleIR *IR)
{
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = FI.second;
        if (endswith(methodName, "__RDY"))
            continue;
        MethodInfo *MIRdy = IR->method[getRdyName(methodName)];
        assert(MIRdy);
        for (auto info: MI->callList) {
            std::string tempCond = getRdyName(info.value->value);
            if (info.cond)
                tempCond += " | " + invertExpr(info.cond);
            if (tree2str(MIRdy->guard) == "1")
                MIRdy->guard = str2tree(tempCond);
            else
                MIRdy->guard = str2tree("(" + tree2str(MIRdy->guard) + ") & (" + tempCond + ")");
        }
    }
}
