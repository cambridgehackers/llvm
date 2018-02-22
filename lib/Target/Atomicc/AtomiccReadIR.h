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
static std::string trimStr(std::string arg)
{
    const char *start = arg.c_str(), *end = start + arg.length() - 1;
    while (start != end && *start == ' ')
        start++;
    while (start != end && *end == ' ')
        --end;
    std::string ret = std::string(start, end+1);
    return ret;
}
std::list<std::string> readNameList;
static void tokenizeStr(std::string arg)
{
    int total = arg.length();
    int index = 0;
    char ch = arg[index++];
    readNameList.clear();
    while(index < total) {
        std::string token;
        if (ch == ' ' || ch == '\t') {
            ch = arg[index++];
        }
        else if (isalpha(ch) || ch == '_' || ch == '$') {
            do {
                token += ch;
                ch = arg[index++];
            } while (isalpha(ch) || isdigit(ch) || ch == '_' || ch == '$');
//printf("[%s:%d] token %s\n", __FUNCTION__, __LINE__, token.c_str());
            readNameList.push_back(token);
        }
        else if (isdigit(ch)) {
            do {
                token += ch;
                ch = arg[index++];
            } while (isdigit(ch) || ch == '.');
        }
        else if (ch == '{') {
            token += ch;
            ch = arg[index++];
            readNameList.pop_back();
        }
        else if (ch == '+' || ch == '-' || ch == '*' || ch == '/' || ch == '%'
            || ch == '}' || ch == '(' || ch == ')' || ch == '<' || ch == '>'
            || ch == '&' || ch == '|' || ch == '^' || ch == '!'
            || ch == '=' || ch == ',' || ch == '?' || ch == ':') {
            token += ch;
            ch = arg[index++];
        }
        else {
printf("[%s:%d] arg '%s' unknown ch %c\n", __FUNCTION__, __LINE__, arg.c_str(), ch);
            exit(-1);
        }
    }
}
std::string scanExpression(const char *val)
{
    const char *startp = val;
    int level = 0;
    while (*val == ' ')
        val++;
    while (*val && ((*val != ' ' && *val != ':' && *val != ',') || level != 0)) {
        if (*val == '(')
            level++;
        else if (*val == ')')
            level--;
        val++;
    }
    return std::string(startp, val);
}
static std::string getExpression()
{
    std::string scanexp = scanExpression(bufp);
    bufp += scanexp.length();
    std::string ret = trimStr(scanexp);
    if (ret[0] == '(' && ret[ret.length()-1] == ')')
        ret = ret.substr(1, ret.length()-2);
    while (*bufp == ' ')
        bufp++;
    return ret;
}
static std::map<std::string, ModuleIR *> mapIndex;
static ModuleIR *lookupIR(std::string ind)
{
    ind = trimStr(ind);
    if (ind == "")
        return nullptr;
    ModuleIR *ret = mapIndex[ind];
    ParseCheck(ret != NULL, "lookupIR = " + ind + " not found");
    return ret;
}
static uint64_t convertType(std::string arg)
{
    if (arg == "")
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
            else if (checkItem("OUTCALL")) {
                std::string      fldName = getToken();
                std::string      type = getToken();
                ModuleIR *lIR = lookupIR(type);
                IR->outcall.push_back(OutcallInterface{fldName, lIR});
            }
            else if (checkItem("PRIORITY")) {
                std::string rule = getToken();
                IR->priority[rule] = getToken();
            }
            else if (checkItem("INTERFACECONNECT")) {
                std::string target = getToken();
                std::string source = getToken();
                ModuleIR *lIR = lookupIR(getToken());
                IR->interfaceConnect.push_back(InterfaceConnectType{target, source, lIR});
            }
            else if (checkItem("FIELD")) {
                int64_t     vecCount = -1;
                unsigned    arrayLen = 0;
                bool        isPtr = checkItem("/Ptr");
                if (checkItem("/Count"))
                    vecCount = atoi(getToken().c_str());
                if (checkItem("/Array"))
                    arrayLen = atoi(getToken().c_str());
                std::string fldName = getToken();
                std::string type = getToken();
                IR->fields.push_back(FieldElement{fldName, vecCount, type, mapIndex[type], arrayLen, isPtr});
            }
            else if (checkItem("METHOD")) {
                MethodInfo *MI = new MethodInfo{""};
                if (checkItem("/Rule"))
                    MI->rule = true;
                std::string methodName = getToken();
                auto insertRead = [&](std::string expr, std::string cond) -> std::string {
                    tokenizeStr(expr);
                    for (auto item: readNameList)
                        MI->meta[MetaRead][item].insert(cond);
                    return expr;
                };
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
                bool foundParen = checkItem("{");
                bool foundIf = false;
                if (!foundParen) {
                    foundIf = checkItem("if");
                    if (!foundIf)
                        MI->type = getToken();
                }
                if (checkItem("="))
                    MI->guard = insertRead(getExpression(), "");
                IR->method[methodName] = MI;
                if (foundIf || (!foundParen && checkItem("if"))) {
                    std::string rdyName = getRdyName(methodName);
                    MethodInfo *MIRdy = new MethodInfo{""};
                    MIRdy->rule = MI->rule;
                    MIRdy->type = "INTEGER_1";
                    MIRdy->guard = getExpression();
                    IR->method[rdyName] = MIRdy;
                }
                if (foundParen || checkItem("{")) {
                    while (readLine() && !checkItem("}")) {
                        if (checkItem("ALLOCA")) {
                            std::string name = getToken();
                            MI->alloca[name] = getToken();
                        }
                        else if (checkItem("STORE")) {
                            std::string cond = insertRead(getExpression(), "");
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression();
                            ParseCheck(checkItem("="), "store = missing");
                            std::string expr = insertRead(bufp, cond);
                            MI->storeList.push_back(StoreListElement{dest, expr, cond, false});
                        }
                        else if (checkItem("LET")) {
                            std::string type = getToken();
                            std::string cond = insertRead(getExpression(), "");
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression();
                            ParseCheck(checkItem("="), "store = missing");
                            std::string expr = insertRead(bufp, cond);
                            MI->storeList.push_back(StoreListElement{dest, expr, cond, true});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            std::string cond = insertRead(getExpression(), "");
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string expr = insertRead(bufp, cond);
                            MI->callList.push_back(CallListElement{expr, cond, isAction});
                            MI->meta[MetaInvoke][expr.substr(0,expr.find("{"))].insert(cond);
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
                if (endswith(methodName, "__RDY"))
                    continue;
                std::string rdyName = getRdyName(methodName);
                if (IR->method[rdyName])
                    continue;
                MethodInfo *MIRdy = new MethodInfo{""};
                MIRdy->rule = MI->rule;
                MIRdy->type = "INTEGER_1";
                MIRdy->guard = "1";
                IR->method[rdyName] = MIRdy;
            }
        }
    }
    for (auto irItem : irSeq)
         promoteGuards(irItem);
}
