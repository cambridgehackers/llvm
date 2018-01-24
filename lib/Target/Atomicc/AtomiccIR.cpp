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
static uint64_t getSize()
{
    return atoi(getToken().c_str());
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
                bool        isPtr = checkItem("/PTR");
                struct ModuleIR *lIR = nullptr;
                std::string fldName = getToken();
                int ind = fldName.find(":");
                if (ind > 0) {
                    lIR = lookupIR(fldName.substr(0,ind));
                    fldName = fldName.substr(ind+1);
                }
                int64_t     vecCount = -1;
                unsigned arrayLen = 0;
                uint64_t size = 0;
                if (checkItem("COUNT"))
                    vecCount = getSize();
                if (checkItem("SIZE"))
                    size = getSize();
                if (checkItem("ARRAY"))
                    arrayLen = getSize();
                IR->fields.push_back(FieldElement{fldName, vecCount, size, lIR, arrayLen, isPtr});
            }
            else if (checkItem("METHOD")) {
                MethodInfo *MI = new MethodInfo{""};
                if (checkItem("/Rule"))
                    MI->rule = true;
                std::string methodName = getToken();
                if (checkItem("SIZE"))
                    MI->size = getSize();
                if (checkItem("="))
                    MI->guard = getExpression();
                IR->method[methodName] = MI;
                if (checkItem("(")) {
                    while (readLine() && !checkItem(")")) {
                        if (checkItem("PARAM")) {
                            std::string name = getToken();
                            ParseCheck(checkItem("SIZE"), "SIZE field missing");
                            MI->params.push_back(ParamElement{name, getSize()});
                        }
                        else if (checkItem("STORE")) {
                            bool isAlloca = checkItem("/Alloca");
                            std::string cond = getExpression();
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression();
                            ParseCheck(checkItem("="), "store = missing");
                            MI->storeList.push_back(StoreListElement{dest, bufp, cond, isAlloca});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            std::string cond = getExpression();
                            ParseCheck(checkItem(":"), "':' missing");
                            MI->callList.push_back(CallListElement{bufp, cond, isAction});
                        }
                        else if (checkItem("METAREAD")) {
                            std::string mname = getExpression();
                            std::string mval = bufp;
                            MI->meta[MetaRead][mname].insert(mval);
                        }
                        else if (checkItem("METAINVOKE")) {
                            std::string mname = getExpression();
                            std::string mval = bufp;
                            MI->meta[MetaInvoke][mname].insert(mval);
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
