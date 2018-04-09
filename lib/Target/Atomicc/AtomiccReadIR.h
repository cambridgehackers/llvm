//===-- AtomiccIR.cpp - Generating IR from LLVM -----===//
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

static char buf[MAX_READ_LINE];
static char *bufp;
static int lineNumber = 0;
static FILE *OStrGlobal;
static std::map<std::string, ModuleIR *> mapIndex;

static ACCExpr *getExpression(void)
{
    const char *startp = bufp;
    int level = 0;
    while (*bufp == ' ')
        bufp++;
    while (*bufp && ((*bufp != ' ' && *bufp != ':' && *bufp != ',') || level != 0)) {
        if (*bufp == '(')
            level++;
        else if (*bufp == ')')
            level--;
        bufp++;
    }
    while (*bufp == ' ')
        bufp++;
    return str2tree(std::string(startp, bufp - startp));
}

static ACCExpr *walkRead (ModuleIR *IR, MethodInfo *MI, ACCExpr *expr, ACCExpr *cond)
{
    if (expr) {
        std::string fieldName = expr->value;
        if (isIdChar(fieldName[0])) {
            if (MI && (!expr->operands.size() || expr->operands.front()->value != "{"))
                MI->meta[MetaRead][fieldName].insert(tree2str(cond));
            int size = -1;
            if (expr->operands.size() && expr->operands.front()->value == "[") {
                ACCExpr *sub = expr->operands.front();
                expr->operands.pop_front();
                std::string post, subscript = tree2str(sub->operands.front());
                sub->operands.clear();
                ACCExpr *next = expr->next;
                if (next && isIdChar(next->value[0])) {
                    if (next->operands.size() && next->operands.front()->value == "{")
                        expr->operands.push_back(next->operands.front());
                    post = next->value;
                    next = next->next;
                    expr->next = next;
                }
                else if (expr->operands.size() && isIdChar(expr->operands.front()->value[0])) {
                    post = expr->operands.front()->value;
                    expr->operands.pop_front();
                }
                for (auto item: IR->fields)
                    if (item.fldName == fieldName) {
                        size = item.vecCount;
                        break;
                    }
printf("[%s:%d] ARRAAA size %d '%s' sub '%s' post '%s'\n", __FUNCTION__, __LINE__, size, fieldName.c_str(), subscript.c_str(), post.c_str());
                expr->value = fieldName + subscript + post;   // replace field name
                if (!isdigit(subscript[0])) {
                    std::string ret;
                    for (int i = 0; i < size - 1; i++)
                        ret += " ( " + subscript + " == " + autostr(i) + " ) ? "
                            + fieldName + autostr(i) + post + " : ";
                    ACCExpr *newTree = str2tree("(" + ret + fieldName + autostr(size - 1) + post + ")");
printf("[%s:%d] NEWTREEFORSUB %s\n", __FUNCTION__, __LINE__, tree2str(newTree).c_str());
                    expr->value = newTree->value;
                    //expr->next = newTree->next;
                    expr->operands.clear();
                    for (auto item: newTree->operands)
                        expr->operands.push_back(item);
printf("[%s:%d] FINALLLLLL %s\n", __FUNCTION__, __LINE__, tree2str(expr).c_str());
                }
            }
        }
        for (auto item: expr->operands)
            walkRead(IR, MI, item, cond);
        walkRead(IR, MI, expr->next, cond);
    }
    return expr;
}

static bool checkItem(const char *val)
{
     while (*bufp == ' ')
         bufp++;
     int len = strlen(val);
//printf("[%s:%d] val %s len %d bufp %s\n", __FUNCTION__, __LINE__, val, len, bufp);
     bool ret = !strncmp(bufp, val, len);
     if (ret)
         bufp += len;
     while (*bufp == ' ')
         bufp++;
     return ret;
}
static void ParseCheck(bool ok, std::string message)
{
    if (!ok) {
        printf("[%s:%d] ERROR: %s: residual %s\n", __FUNCTION__, __LINE__, message.c_str(), bufp);
        printf("full line number %d: %s\n", lineNumber, buf);
        exit(-1);
    }
}
static bool readLine(void)
{
    if (fgets(buf, sizeof(buf), OStrGlobal) == NULL)
        return false;
    buf[strlen(buf) - 1] = 0;
    bufp = buf;
    lineNumber++;
    return true;
}
static std::string getToken()
{
    char *startp = bufp;
    while (*bufp == ' ')
        bufp++;
    while (*bufp && *bufp != ' ')
        bufp++;
    std::string ret = std::string(startp, bufp);
    while (*bufp == ' ')
        bufp++;
    return ret;
}

void readModuleIR(std::list<ModuleIR *> &irSeq, FILE *OStr)
{
    OStrGlobal = OStr;
    while (readLine()) {
        bool ext = checkItem("EMODULE");
        ParseCheck(ext || checkItem("MODULE"), "Module header missing");
        ModuleIR *IR = new ModuleIR;
        if (!ext)
            irSeq.push_back(IR);
        IR->name = getToken();
        ParseCheck(checkItem("{"), "Module '{' missing");
        mapIndex[IR->name] = IR;
        while (readLine() && !checkItem("}")) {
            if (checkItem("SOFTWARE")) {
                IR->softwareName.push_back(getToken());
            }
            else if (checkItem("PRIORITY")) {
                std::string rule = getToken();
                IR->priority[rule] = getToken();
            }
            else if (checkItem("INTERFACECONNECT")) {
                std::string target = getToken();
                std::string source = getToken();
                std::string type = getToken();
                IR->interfaceConnect.push_back(InterfaceConnectType{target, source, type});
            }
            else if (checkItem("UNION")) {
                std::string type = getToken();
                IR->unionList.push_back(UnionItem{getToken(), type});
            }
            else if (checkItem("FIELD")) {
                int64_t     vecCount = -1;
                unsigned    arrayLen = 0;
                bool        isPtr = checkItem("/Ptr");
                if (checkItem("/Count"))
                    vecCount = atoi(getToken().c_str());
                if (checkItem("/Array"))
                    arrayLen = atoi(getToken().c_str());
                std::string type = getToken();
                std::string fldName = getToken();
                IR->fields.push_back(FieldElement{fldName, vecCount, type, arrayLen, isPtr});
            }
            else if (checkItem("INTERFACE")) {
                int64_t     vecCount = -1;
                unsigned    arrayLen = 0;
                bool        isPtr = checkItem("/Ptr");
                if (checkItem("/Count"))
                    vecCount = atoi(getToken().c_str());
                if (checkItem("/Array"))
                    arrayLen = atoi(getToken().c_str());
                std::string type = getToken();
                std::string fldName = getToken();
                IR->interfaces.push_back(FieldElement{fldName, vecCount, type, arrayLen, isPtr});
            }
            else if (checkItem("METHOD")) {
                MethodInfo *MI = new MethodInfo{nullptr};
                if (checkItem("/Rule"))
                    MI->rule = true;
                std::string methodName = getToken();
                if (checkItem("(")) {
                    bool first = true;
                    while (!checkItem(")")) {
                        if (!first)
                            ParseCheck(checkItem(","), "',' missing");
                        std::string type = getToken();
                        MI->params.push_back(ParamElement{getToken(), type});
                        first = false;
                    }
                }
                bool foundOpenBrace = checkItem("{");
                bool foundIf = false;
                if (!foundOpenBrace) {
                    foundIf = checkItem("if");
                    if (!foundIf)
                        MI->type = getToken();
                }
                if (checkItem("="))
                    MI->guard = walkRead(IR, MI, getExpression(), nullptr);
                IR->method[methodName] = MI;
                if (foundIf || (!foundOpenBrace && checkItem("if"))) {
                    MethodInfo *MIRdy = new MethodInfo{nullptr};
                    MIRdy->rule = MI->rule;
                    MIRdy->type = "INTEGER_1";
                    MIRdy->guard = walkRead(IR, nullptr, getExpression(), nullptr);
                    IR->method[getRdyName(methodName)] = MIRdy;
                }
                if (foundOpenBrace || checkItem("{")) {
                    while (readLine() && !checkItem("}")) {
                        if (checkItem("ALLOCA")) {
                            std::string type = getToken();
                            std::string name = getToken();
                            MI->alloca[name] = type;
                        }
                        else if (checkItem("STORE")) {
                            ACCExpr *cond = walkRead(IR, MI, getExpression(), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *dest = walkRead(IR, nullptr, getExpression(), nullptr);
                            ParseCheck(checkItem("="), "store = missing");
                            ACCExpr *expr = walkRead(IR, MI, str2tree(bufp), cond);
                            MI->storeList.push_back(StoreListElement{dest, expr, cond});
                        }
                        else if (checkItem("LET")) {
                            std::string type = getToken();
                            ACCExpr *cond = walkRead(IR, MI, getExpression(), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *dest = walkRead(IR, nullptr, getExpression(), nullptr);
                            ParseCheck(checkItem("="), "store = missing");
                            ACCExpr *expr = walkRead(IR, MI, str2tree(bufp), cond);
                            MI->letList.push_back(LetListElement{dest, expr, cond, type});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            ACCExpr *cond = walkRead(IR, MI, getExpression(), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *expr = walkRead(IR, MI, str2tree(bufp), cond);
                            MI->callList.push_back(CallListElement{expr, cond, isAction});
                            if (isIdChar(expr->value[0]) && expr->operands.size() && expr->operands.front()->value == "{")
                                MI->meta[MetaInvoke][expr->value].insert(tree2str(cond));
                            else {
                                printf("[%s:%d] called method name not found %s\n", __FUNCTION__, __LINE__, tree2str(expr).c_str());
dumpExpr("READCALL", expr);
                                exit(-1);
                            }
                        }
                        else
                            ParseCheck(false, "unknown method item");
                    }
                }
            }
            else
                ParseCheck(false, "unknown module item");
            for (auto item: IR->method) {
                std::string methodName = item.first;
                MethodInfo *MI = item.second;
                std::string rdyName = getRdyName(methodName);
                if (!endswith(methodName, "__RDY") && !IR->method[rdyName]) {
                    MethodInfo *MIRdy = new MethodInfo{nullptr};
                    MIRdy->rule = MI->rule;
                    MIRdy->type = "INTEGER_1";
                    MIRdy->guard = allocExpr("1");
                    IR->method[rdyName] = MIRdy;
                }
            }
        }
    }
    for (auto irItem : irSeq)
         promoteGuards(irItem);
}
