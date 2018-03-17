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

enum TokType {TOK_NONE, TOK_ID, TOK_NUMBER, TOK_ARITHOP, TOK_RELOP, TOK_LBRACE, TOK_MISCOP,
    TOK_EOF};
typedef struct {
    TokType type;
    std::string value;
} TokenValue;
typedef struct ACCExpr {
    std::string op;
    std::list<ACCExpr *>operands;
    ACCExpr *next;
    std::string value;
} ACCExpr;

static char buf[MAX_READ_LINE];
static char *bufp;
static int lineNumber = 0;
static FILE *OStrGlobal;
std::list<std::string> readNameList;

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

bool isIdChar(char ch)
{
    return isalpha(ch) || ch == '_' || ch == '$';
}

static std::string lexString;
static int lexTotal;
static int lexIndex;
static char lexChar;

static ACCExpr *allocExpr(std::string value)
{
    ACCExpr *ret = new ACCExpr;
    ret->op = "";
    ret->value = value;
    ret->operands.clear();
    ret->next = nullptr;
    return ret;
}

static TokenValue get1Token(void)
{
    std::string lexToken;
    auto getNext = [&] (void) -> void {
        lexToken += lexChar;
        lexChar = lexString[lexIndex++];
    };

    while (lexChar == ' ' || lexChar == '\t') {
        lexChar = lexString[lexIndex++];
    }
    if(lexIndex > lexTotal || lexChar == 0)
        return TokenValue{TOK_EOF, ""};
    if (isIdChar(lexChar)) {
        do {
            getNext();
        } while (isIdChar(lexChar) || isdigit(lexChar));
//printf("[%s:%d] lexToken %s\n", __FUNCTION__, __LINE__, lexToken.c_str());
        readNameList.push_back(lexToken);
        return TokenValue{TOK_ID, lexToken};
    }
    else if (isdigit(lexChar)) {
        do {
            getNext();
        } while (isdigit(lexChar) || lexChar == '.');
        return TokenValue{TOK_NUMBER, lexToken};
    }
    else if (lexChar == '+' || lexChar == '-' || lexChar == '*' || lexChar == '&' || lexChar == '|') {
        do {
            getNext();
        } while (lexChar == lexToken[0]);
        return TokenValue{TOK_ARITHOP, lexToken};
    }
    else if (lexChar == '=' || lexChar == '<' || lexChar == '>' || lexChar == '!') {
        do {
            getNext();
        } while (lexChar == '=' || lexChar == '<' || lexChar == '>');
        return TokenValue{TOK_RELOP, lexToken};
    }
    else if (lexChar == '{') {
        getNext();
        if (readNameList.size() > 0)
            readNameList.pop_back();
        return TokenValue{TOK_LBRACE, lexToken};
    }
    else if (lexChar == '/' || lexChar == '%'
        || lexChar == '}' || lexChar == '(' || lexChar == ')' || lexChar == '^'
        || lexChar == '[' || lexChar == ']'
        || lexChar == ',' || lexChar == '?' || lexChar == ':' || lexChar == ';') {
        getNext();
        return TokenValue{TOK_MISCOP, lexToken};
    }
    printf("[%s:%d] lexString '%s' unknown lexChar %c %x\n", __FUNCTION__, __LINE__, lexString.c_str(), lexChar, lexChar);
    exit(-1);
}

static std::string treePost(ACCExpr *arg)
{
    std::string ret;
    if (arg->value == "[")
        return " ]";
    else if (arg->value == "(")
        return " )";
    else if (arg->value == "{")
        return " }";
    return ret;
}

static ACCExpr *get1Tokene(void)
{
    TokenValue tok = get1Token();
    if (tok.type == TOK_EOF)
        return nullptr;
    ACCExpr *ret = allocExpr(tok.value), *etok;
    if (ret->value == "[" || ret->value == "(" || ret->value == "{")
        while ((etok = get1Tokene()) && etok->value != treePost(ret).substr(1))
            ret->operands.push_back(etok);
    return ret;
}

static ACCExpr *list2tree(ACCExpr *ret)
{
     if (!ret)
         return nullptr;
//printf("[%s:%d] ret %s\n", __FUNCTION__, __LINE__, tree2str(ret).c_str());
     ACCExpr *tok = get1Tokene();
     if (isIdChar(ret->value[0])) {
         if (tok && tok->value == "[") {
             ret->operands.push_back(tok);
             ACCExpr *tt = tok;
             tok = get1Tokene();
             if (tok && tok->value[0] == '$') {
                 tt->next = tok;
                 tok = get1Tokene();
             }
         }
     }
     ret->next = list2tree(tok);
     return ret;
}

static ACCExpr *str2tree(std::string arg)
{
    lexString = arg;
    lexTotal = lexString.length();
    lexIndex = 0;
    lexChar = lexString[lexIndex++];
    readNameList.clear();
    return list2tree(get1Tokene());
}

static std::string tree2str(ACCExpr *arg)
{
    std::string ret;
    ret += arg->value;
    for (auto item: arg->operands)
        ret += " " + tree2str(item);
    ret += treePost(arg);
    if (arg->next)
        ret += " " + tree2str(arg->next);
    return ret;
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

std::string expandExpression(ModuleIR *IR, ACCExpr *expr)
{
    std::string ret = expr->value;
    if (isIdChar(ret[0]) && expr->operands.size()) {
        int size = -1;
        std::string subscript, sep, post, fieldName = ret;
        ACCExpr *sub = expr->operands.front();
        if (sub->next)
            post = sub->next->value;
        for (auto item: IR->fields)
            if (item.fldName == fieldName) {
                size = item.vecCount;
                break;
            }
        for (auto item: sub->operands) {
            if (item->value == "]")
                break;
            subscript += sep + item->value;
            sep = " ";
        }
printf("[%s:%d] ARRAAA size %d '%s' sub '%s' post '%s'\n", __FUNCTION__, __LINE__, size, fieldName.c_str(), subscript.c_str(), post.c_str());
        ret = fieldName + subscript + post;
        if (!isdigit(subscript[0])) {
            ret = " ( ";
            for (int i = 0; i < size - 1; i++)
                ret += " ( " + subscript + " == " + autostr(i) + " ) ? "
                    + fieldName + autostr(i) + post + " : ";
            ret += fieldName + autostr(size - 1) + post + " ) ";
        }
printf("[%s:%d] expand '%s'\n", __FUNCTION__, __LINE__, ret.c_str());
    }
    else
        for (auto item: expr->operands)
            ret += " " + expandExpression(IR, item);
    ret += treePost(expr);
    if (expr->next)
        ret += " " + expandExpression(IR, expr->next);
    return ret;
}

static std::string getExpression(ModuleIR *IR)
{
    std::string scanexp = scanExpression(bufp);
    bufp += scanexp.length();
    std::string ret = trimStr(scanexp);
    if (ret[0] == '(' && ret[ret.length()-1] == ')')
        ret = ret.substr(1, ret.length()-2);
    while (*bufp == ' ')
        bufp++;
    if (ret == "")
        return ret;
    return expandExpression(IR, str2tree(ret));
}
static std::map<std::string, ModuleIR *> mapIndex;
static ModuleIR *lookupIR(std::string ind)
{
    ind = trimStr(ind);
    if (ind == "")
        return nullptr;
    ModuleIR *ret = mapIndex[ind];
    //ParseCheck(ret != NULL, "lookupIR = " + ind + " not found");
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
                MethodInfo *MI = new MethodInfo{""};
                if (checkItem("/Rule"))
                    MI->rule = true;
                std::string methodName = getToken();
                auto insertRead = [&](std::string expr, std::string cond) -> std::string {
                    ACCExpr *exprp = str2tree(expr);
                    for (auto item: readNameList)
                        MI->meta[MetaRead][item].insert(cond);
                    if (!exprp)
                        return "";
                    return expandExpression(IR, exprp);
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
                    MI->guard = insertRead(getExpression(IR), "");
                IR->method[methodName] = MI;
                if (foundIf || (!foundParen && checkItem("if"))) {
                    std::string rdyName = getRdyName(methodName);
                    MethodInfo *MIRdy = new MethodInfo{""};
                    MIRdy->rule = MI->rule;
                    MIRdy->type = "INTEGER_1";
                    MIRdy->guard = getExpression(IR);
                    IR->method[rdyName] = MIRdy;
                }
                if (foundParen || checkItem("{")) {
                    while (readLine() && !checkItem("}")) {
                        if (checkItem("ALLOCA")) {
                            std::string type = getToken();
                            std::string name = getToken();
                            MI->alloca[name] = type;
                        }
                        else if (checkItem("STORE")) {
                            std::string cond = insertRead(getExpression(IR), "");
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression(IR);
                            ParseCheck(checkItem("="), "store = missing");
                            std::string expr = insertRead(bufp, cond);
                            MI->storeList.push_back(StoreListElement{dest, expr, cond});
                        }
                        else if (checkItem("LET")) {
                            std::string type = getToken();
                            std::string cond = insertRead(getExpression(IR), "");
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string dest = getExpression(IR);
                            ParseCheck(checkItem("="), "store = missing");
                            std::string expr = insertRead(bufp, cond);
                            MI->letList.push_back(LetListElement{dest, expr, cond, type});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            std::string cond = insertRead(getExpression(IR), "");
                            ParseCheck(checkItem(":"), "':' missing");
                            std::string expr = insertRead(bufp, cond);
                            MI->callList.push_back(CallListElement{expr, cond, isAction});
                            MI->meta[MetaInvoke][trimStr(expr.substr(0,expr.find("{")))].insert(cond);
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
