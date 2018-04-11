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
    return mapIndex[ind];
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
    ACCExpr *itemList = allocExpr(",");
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
            itemList->operands.push_back(allocExpr(fitem.name));
        else
            setAssign(fitem.name, allocExpr(fldName + "[" + autostr(offset) + ":" + autostr(upper) + "]"), fitem.type);
    }
    if (itemList->operands.size())
        setAssign(fldName, allocExpr("{", itemList), type);
}

static void addRead(MetaSet &list, ACCExpr *cond)
{
    if(isIdChar(cond->value[0]))
        list.insert(cond->value);
    for (auto item: cond->operands)
        addRead(list, item);
}

static void walkRead (MethodInfo *MI, ACCExpr *expr, ACCExpr *cond)
{
    if (!expr)
        return;
    for (auto item: expr->operands)
        walkRead(MI, item, cond);
    std::string fieldName = expr->value;
    if (isIdChar(fieldName[0]) && cond && (!expr->operands.size() || expr->operands.front()->value != "{"))
        addRead(MI->meta[MetaRead][fieldName], cond);
}

static void walkRef (ACCExpr *expr)
{
    std::string item = expr->value;
    if (isIdChar(item[0]))
        refList[item] = true;
    for (auto item: expr->operands)
        walkRef(item);
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
            bool operand = checkOperand(item->value) || item->value == "," || item->value == "?" || expr->operands.size() == 1;
            ret += sep;
            if (!operand)
                ret += "( ";
            ret += walkTree(item, changed);
            if (!operand)
                ret += " )";
            sep = " " + op + " ";
            if (op == "?")
                op = ":";
        }
    }
    ret += treePost(expr);
    return ret;
}

std::string findType(std::string name)
{
//printf("[%s:%d] name %s\n", __FUNCTION__, __LINE__, name.c_str());
    if (regList.find(name) != regList.end())
        return regList[name];
    else if (typeList.find(name) != typeList.end())
        return typeList[name];
    else if (wireList.find(name) != wireList.end())
        return wireList[name];
    else if (assignList.find(name) != assignList.end())
        return assignList[name].type;
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
    std::map<std::string, ACCExpr *> enableList;
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
                expandStruct(IR, fldName, item.type, regList, 1, true);
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
        if (!endswith(methodName, "__RDY"))
            walkRead(MI, MI->guard, nullptr);
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
            walkRead(MI, info.cond, nullptr);
            walkRead(MI, info.value, info.cond);
            std::list<FieldItem> fieldList;
            getFieldList(fieldList, "", info.type, true);
            for (auto fitem : fieldList) {
                std::string dest = info.dest->value + fitem.name;
                std::string src = info.value->value + fitem.name;
                typeList[dest] = fitem.type;
                typeList[src] = fitem.type;
                muxValueList[dest].push_back(MuxValueEntry{info.cond, allocExpr(src)});
            }
        }
        for (auto info: MI->callList) {
            if (isIdChar(info->value->value[0]) && info->value->operands.size() && info->value->operands.front()->value == "{")
                MI->meta[MetaInvoke][info->value->value].insert(tree2str(info->cond));
            else {
                printf("[%s:%d] called method name not found %s\n", __FUNCTION__, __LINE__, tree2str(info->value).c_str());
dumpExpr("READCALL", info->value);
                    exit(-1);
            }
            walkRead(MI, info->cond, nullptr);
            walkRead(MI, info->value, info->cond);
            if (!info->isAction)
                continue;
            ACCExpr *tempCond = str2tree(methodName);
            if (info->cond) {
                ACCExpr *temp = info->cond;
                if (temp->value != "&")
                    temp = allocExpr("&", temp);
                temp->operands.push_back(tempCond);
                tempCond = temp;
            }
            std::string calledName = info->value->value;
printf("[%s:%d] CALLLLLL '%s'\n", __FUNCTION__, __LINE__, calledName.c_str());
            if (!info->value->operands.size() || info->value->operands.front()->value != "{") {
                printf("[%s:%d] incorrectly formed call expression\n", __FUNCTION__, __LINE__);
                exit(-1);
            }
            // 'Or' together ENA lines from all invocations of a method from this class
            if (info->isAction) {
                if (!enableList[calledName])
                    enableList[calledName] = allocExpr("||");
                enableList[calledName]->operands.push_back(tempCond);
            }
            MethodInfo *CI = lookupQualName(IR, calledName);
            if (!CI) {
                printf("[%s:%d] method %s not found\n", __FUNCTION__, __LINE__, calledName.c_str());
                exit(-1);
            }
            auto AI = CI->params.begin();
            std::string pname = calledName.substr(0, calledName.length()-5) + MODULE_SEPARATOR;
            int argCount = CI->params.size();
            ACCExpr *param = info->value->operands.front()->operands.front();
printf("[%s:%d] param '%s'\n", __FUNCTION__, __LINE__, tree2str(param).c_str());
//dumpExpr("param", param);
            auto setParam = [&] (const ACCExpr *item) -> void {
                if(argCount-- > 0) {
                    std::string scanexp = tree2str(item);
printf("[%s:%d] infmuxVL[%s] = cond '%s' tree '%s'\n", __FUNCTION__, __LINE__, (pname + AI->name).c_str(),
tree2str(tempCond).c_str(), scanexp.c_str());
                    muxValueList[pname + AI->name].push_back(MuxValueEntry{tempCond, str2tree(scanexp)});
                    typeList[pname + AI->name] = AI->type;
                    AI++;
                }
            };
            if (param) {
                if (param->value == ",")
                    for (auto item: param->operands)
                        setParam(item);
                else
                    setParam(param);
            }
        }
    }
    for (auto item: enableList)
        setAssign(item.first, item.second, "INTEGER_1");
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
        MethodInfo *MI = FI.second;
        bool alwaysSeen = false;
        for (auto info: FI.second->storeList) {
            walkRead(MI, info.cond, nullptr);
            walkRead(MI, info.value, info.cond);
    ACCExpr *expr = info.dest;
    if (expr->value == "?") {
        int i = 0;
        for (auto item: expr->operands)
            if (i++ == 1) {
                expr = item;
                break;
            }
    }
std::string destType = findType(expr->value);
if (destType == "") {
printf("[%s:%d] typenotfound %s\n", __FUNCTION__, __LINE__, tree2str(info.dest).c_str());
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
            ACCExpr *tempCond = allocExpr(getRdyName(info->value->value));
            if (info->cond) {
                ACCExpr *icon = invertExpr(info->cond);
                if (icon->value != "|")
                    icon = allocExpr("|", icon);
                icon->operands.push_back(tempCond);
                tempCond = icon;
            }
            if (MIRdy->guard->value == "1")
                MIRdy->guard = allocExpr("&");
            else if (MIRdy->guard->value != "&")
                MIRdy->guard = allocExpr("&", MIRdy->guard);
            MIRdy->guard->operands.push_back(tempCond);
        }
    }
}

static void walkSubscript (ModuleIR *IR, ACCExpr *expr)
{
    if (!expr)
        return;
    for (auto item: expr->operands)
        walkSubscript(IR, item);
    std::string fieldName = expr->value;
    if (!isIdChar(fieldName[0]) || !expr->operands.size() || expr->operands.front()->value != "[")
        return;
    ACCExpr *subscript = expr->operands.front()->operands.front();
    expr->operands.pop_front();
    std::string post;
    if (expr->operands.size() && isIdChar(expr->operands.front()->value[0])) {
        post = expr->operands.front()->value;
        expr->operands.pop_front();
    }
    int size = -1;
    for (auto item: IR->fields)
        if (item.fldName == fieldName) {
            size = item.vecCount;
            break;
        }
printf("[%s:%d] ARRAAA size %d '%s' post '%s'\n", __FUNCTION__, __LINE__, size, fieldName.c_str(), post.c_str());
    assert (!isdigit(subscript->value[0]));
    std::string lastElement = fieldName + autostr(size - 1) + post;
    expr->value = lastElement; // if only 1 element
    for (int i = 0; i < size - 1; i++) {
        std::string ind = autostr(i);
        expr->value = "?";
        expr->operands.push_back(allocExpr("==", subscript, allocExpr(ind)));
        expr->operands.push_back(allocExpr(fieldName + ind + post));
        if (i == size - 2)
            expr->operands.push_back(allocExpr(lastElement));
        else {
            ACCExpr *nitem = allocExpr("");
            expr->operands.push_back(nitem);
            expr = nitem;
        }
    }
}
static ACCExpr *findSubscript (ModuleIR *IR, ACCExpr *expr, int &size, std::string &fieldName, ACCExpr **subscript, std::string &post)
{
    if (isIdChar(expr->value[0]) && expr->operands.size() && expr->operands.front()->value == "[") {
        fieldName = expr->value;
        *subscript = expr->operands.front()->operands.front();
        expr->operands.pop_front();
        if (expr->operands.size() && isIdChar(expr->operands.front()->value[0])) {
            post = expr->operands.front()->value;
            expr->operands.pop_front();
        }
        for (auto item: IR->fields)
            if (item.fldName == expr->value) {
                size = item.vecCount;
                break;
            }
        return expr;
    }
    for (auto item: expr->operands)
        if (ACCExpr *ret = findSubscript(IR, item, size, fieldName, subscript, post))
            return ret;
    return nullptr;
}
static ACCExpr *cloneReplaceTree (ACCExpr *expr, ACCExpr *target)
{
    ACCExpr *newExpr = allocExpr(expr->value);
    if (expr != target) {
        for (auto item: expr->operands)
            newExpr->operands.push_back(cloneReplaceTree(item, target));
        return newExpr;
    }
    for (auto item: expr->operands)
        newExpr->operands.push_back(item);
    return newExpr;
}

void generateModuleIR(std::list<ModuleIR *> &irSeq, FILE *OStrVH, FILE *OStrV)
{
    for (auto IR : irSeq) {
        for (auto item: IR->method) {
            std::string methodName = item.first;
            MethodInfo *MI = item.second;
            std::string rdyName = getRdyName(methodName);
            walkSubscript(IR, MI->guard);
            for (auto item: MI->storeList) {
                walkSubscript(IR, item.cond);
                walkSubscript(IR, item.dest);
                walkSubscript(IR, item.value);
            }
            for (auto item: MI->letList) {
                walkSubscript(IR, item.cond);
                walkSubscript(IR, item.dest);
                walkSubscript(IR, item.value);
            }
            for (auto item: MI->callList)
                walkSubscript(IR, item->cond);
            for (auto item: MI->callList) {
                int size = -1;
                ACCExpr *cond = item->cond, *subscript = nullptr;
                std::string fieldName, post;
                if (ACCExpr *expr = findSubscript(IR, item->value, size, fieldName, &subscript, post)) {
                    for (int ind = 0; ind < size; ind++) {
                        ACCExpr *newCond = allocExpr("==", subscript, allocExpr(autostr(ind)));
                        if (cond)
                            newCond = allocExpr("&", cond, newCond);
                        expr->value = fieldName + autostr(ind) + post;
                        if (ind == 0)
                            item->cond = newCond;
                        else
                            MI->callList.push_back(new CallListElement{
                                cloneReplaceTree(item->value, expr), newCond, item->isAction});
                    }
                    expr->value = fieldName + "0" + post;
                }
            }
        }
        promoteGuards(IR);
        // Only generate verilog for modules derived from Module
        generateModuleDef(IR, OStrV);
        // now generate the verilog header file '.vh'
        metaGenerate(IR, OStrVH);
    }
}
