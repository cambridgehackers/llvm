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
#include <stdio.h>
#include "llvm/ADT/StringExtras.h"

using namespace llvm;

#include "AtomiccDecl.h"

/*
 * Generate Module info into IR
 */
void generateModuleIR(ModuleIR *IR, bool isModule, FILE *OStr)
{
    static std::string metaName[] = {"METANONE", "METAREAD ", "METAINVOKE "};
    fprintf(OStr, "%sMODULE %s = %d (\n", isModule ? "" : "E", IR->name.c_str(), IR->sequence);
    for (auto item: IR->softwareName)
        if (item.second)
            fprintf(OStr, "    SOFTWARE %s\n", item.first.c_str());
    for (auto item: IR->outcall)
        fprintf(OStr, "    OUTCALL %s = %d\n", item.fldName.c_str(), item.IR->sequence);
    for (auto item: IR->ruleFunctions)
        if (item.second)
            fprintf(OStr, "    RULE %s\n", item.first.c_str());
    for (auto item: IR->priority)
        fprintf(OStr, "    PRIORITY %s %s\n", item.first.c_str(), item.second.c_str());
    for (auto item: IR->interfaceConnect)
        fprintf(OStr, "    INTERFACECONNECT %s %s %d\n", item.target.c_str(), item.source.c_str(), item.IR->sequence);
    for (auto item: IR->fields) {
        std::string irstr;
        if (item.IR)
            irstr = utostr(item.IR->sequence) + ":";
        std::string temp = item.fldName;
        if (item.vecCount != -1)
            temp += " VEC " + utostr(item.vecCount);
        if (item.arrRange != "")
            temp += " RANGE " + item.arrRange;
        if (item.typeStr != "")
            temp += " FORMAT " + item.typeStr;
        fprintf(OStr, "    FIELD%s %s%s\n", item.isPtr ? "/PTR ": "", irstr.c_str(), temp.c_str());
    }
    for (auto item: IR->method) {
        std::list<std::string> mlines;
        MethodInfo *MI = item.second;
        std::string temp = item.first;
        if (MI->retArrRange != "")
            temp += " RANGE " + MI->retArrRange;
        if (MI->guard != "")
            temp += " = (" + MI->guard + ")";
        fprintf(OStr, "    METHOD%s%s", MI->action ? "/Action ":" ", temp.c_str());
        for (auto litem: MI->params)
            mlines.push_back("PARAM " + litem.name + " " + litem.arrRange);
        for (auto litem: MI->storeList) {
            std::string alloc = " ";
            if (litem.isAlloca)
                alloc = "/Alloca ";
            mlines.push_back("STORE" + alloc + litem.cond + ":" + litem.dest + " = " + litem.value);
        }
        for (auto litem: MI->callList)
            mlines.push_back("CALL" + std::string(litem.isAction ? "/Action ":" ")
                + litem.cond + ":" + litem.value);

        for (int index = MetaRead; index != MetaMax; index++)
            for (auto litem: MI->meta[index])
                for (auto sitem: litem.second)
                    mlines.push_back(metaName[index] + litem.first + " " + sitem);
        if (mlines.size())
            fprintf(OStr, " (");
        fprintf(OStr, "\n");
        for (auto line: mlines)
             fprintf(OStr, "        %s\n", line.c_str());
        if (mlines.size())
            fprintf(OStr, "    )\n");
    }
    fprintf(OStr, ")\n");
}

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
static std::string getCondition()
{
    char *startp = bufp;
    while (*bufp == ' ')
        bufp++;
    while (*bufp && *bufp != ':')
        bufp++;
    std::string ret = std::string(startp, bufp);
    bufp++; // skip ':'
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
    while (*bufp && (*bufp != ' ' || level != 0)) {
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
static std::map<int, ModuleIR *> mapIndex;
static ModuleIR *lookupIR(std::string ind)
{
    ind = trimStr(ind);
    if (ind == "")
        return nullptr;
    int index = atoi(ind.c_str());
    ModuleIR *ret = mapIndex[index];
    ParseCheck(ret != NULL, "lookupIR = " + autostr(index) + " not found");
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
        ParseCheck(checkItem("="), "Module = <sequence> missing");
        IR->sequence = atoi(getToken().c_str());
        ParseCheck(checkItem("("), "Module '(' missing");
        mapIndex[IR->sequence] = IR;
        while (readLine() && !checkItem(")")) {
            if (checkItem("SOFTWARE")) {
                IR->softwareName[getToken()] = 1;
            }
            else if (checkItem("OUTCALL")) {
                std::string      fldName = getToken();
                ParseCheck(checkItem("="), "outcall = missing");
                ModuleIR *lIR = lookupIR(getToken());
                IR->outcall.push_back(OutcallInterface{fldName, lIR});
            }
            else if (checkItem("RULE")) {
                IR->ruleFunctions[getToken()] = true;
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
                std::string arrRange;
                std::string typeStr;
                if (checkItem("VEC"))
                    vecCount = atoi(getToken().c_str());
                if (checkItem("RANGE"))
                    arrRange = getToken();
                if (checkItem("FORMAT"))
                    typeStr = bufp;
                IR->fields.push_back(FieldElement{fldName, vecCount, arrRange, lIR, typeStr, isPtr});
            }
            else if (checkItem("METHOD")) {
                MethodInfo *MI = new MethodInfo{""};
                MI->action = checkItem("/Action");
                std::string methodName = getToken();
                if (checkItem("RANGE"))
                    MI->retArrRange = getToken();
                if (checkItem("="))
                    MI->guard = getExpression();
                IR->method[methodName] = MI;
                if (checkItem("(")) {
                    while (readLine() && !checkItem(")")) {
                        if (checkItem("PARAM")) {
                            std::string name = getToken();
                            std::string arrRange = getToken();
                            MI->params.push_back(ParamElement{arrRange, name});
                        }
                        else if (checkItem("STORE")) {
                            bool isAlloca = checkItem("/Alloca");
                            std::string cond = getCondition();
                            std::string dest = getExpression();
                            ParseCheck(checkItem("="), "store = missing");
                            std::string value = bufp;
                            MI->storeList.push_back(StoreListElement{dest, value, cond, isAlloca});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            std::string cond = getCondition();
                            std::string value = bufp;
                            MI->callList.push_back(CallListElement{value, cond, isAction});
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
