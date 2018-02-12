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
static std::string getExpression()
{
    char *startp = bufp;
    int level = 0;
    while (*bufp == ' ')
        bufp++;
    while (*bufp && ((*bufp != ' ' && *bufp != ':') || level != 0)) {
        if (*bufp == '(')
            level++;
        else if (*bufp == ')')
            level--;
        bufp++;
    }
    std::string ret = trimStr(std::string(startp, bufp));
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
    if (auto IR = lookupIR(bp))
        return IR->size;
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
        IR->size = atoi(getToken().c_str());
        ParseCheck(checkItem("("), "Module '(' missing");
        mapIndex[IR->name] = IR;
        while (readLine() && !checkItem(")")) {
            if (checkItem("SOFTWARE")) {
                IR->softwareName.push_back(getToken());
            }
            else if (checkItem("OUTCALL")) {
                std::string      fldName = getToken();
                ParseCheck(checkItem("="), "outcall = missing");
                ModuleIR *lIR = lookupIR(getToken());
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
                bool foundParen = checkItem("(");
                if (!foundParen)
                    MI->type = getToken();
                if (checkItem("="))
                    MI->guard = getExpression();
                IR->method[methodName] = MI;
                if (foundParen || checkItem("(")) {
                    while (readLine() && !checkItem(")")) {
                        if (checkItem("PARAM")) {
                            std::string name = getToken();
                            MI->params.push_back(ParamElement{name, getToken()});
                        }
                        else if (checkItem("ALLOCA")) {
                            std::string name = getToken();
                            MI->alloca[name] = getToken();
                        }
                        else if (checkItem("STORE")) {
                            std::string cond = getExpression();
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression();
                            ParseCheck(checkItem("="), "store = missing");
                            std::string expr = bufp;
                            MI->storeList.push_back(StoreListElement{dest, expr, cond, false});
                        }
                        else if (checkItem("LET")) {
                            std::string type = getToken();
                            std::string cond = getExpression();
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression();
                            ParseCheck(checkItem("="), "store = missing");
                            std::string expr = bufp;
                            MI->storeList.push_back(StoreListElement{dest, expr, cond, true});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            std::string cond = getExpression();
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string expr = bufp;
                            if (isAction)
                                MI->callList.push_back(CallListElement{expr, cond, isAction});
                            MI->meta[MetaInvoke][expr.substr(0,expr.find("{"))].insert(cond);
                        }
                        else if (checkItem("METAREAD")) {
                            std::string mname = getExpression();
                            MI->meta[MetaRead][mname].insert(bufp);
                        }
                        else
                            ParseCheck(false, "unknown method item");
                    }
                }
            }
            else
                ParseCheck(false, "unknown module item");
        }
    }
}
