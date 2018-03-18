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
    ret->param = nullptr;
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

static ACCExpr *get1Tokene(ACCExpr *prev)
{
    TokenValue tok = get1Token();
    if (tok.type == TOK_EOF)
        return nullptr;
    ACCExpr *etok, *ret = allocExpr(tok.value), *plist = nullptr, *retptr = ret;
    if (prev) {
        if (isIdChar(prev->value[0]) && ret->value == "[") {
            prev->operands.push_back(ret);
            retptr = prev;
        }
        else
            prev->next = ret;
    }
    if (ret->value == "[" || ret->value == "(" || ret->value == "{") {
        while ((etok = get1Tokene(plist)) && etok->value != treePost(ret).substr(1)) {
            if (!plist)
                ret->param = etok;
            plist = etok;
        }
        if (plist)
            plist->next = nullptr;
    }
    return retptr;
}

static ACCExpr *str2tree(std::string arg)
{
    lexString = arg;
    lexTotal = lexString.length();
    lexIndex = 0;
    lexChar = lexString[lexIndex++];
    ACCExpr *tok = get1Tokene(nullptr);
    ACCExpr *prev = tok;
    if (tok)
        while ((prev = get1Tokene(prev)))
            ;
    return tok;
}

static std::string tree2str(ACCExpr *arg)
{
    std::string ret;
    if (!arg)
        return "";
    ret += arg->value;
    for (auto item: arg->operands)
        ret += " " + tree2str(item);
    if (arg->param)
        ret += " " + tree2str(arg->param);
    ret += treePost(arg);
    if (arg->next)
        ret += " " + tree2str(arg->next);
    return ret;
}

static void dumpExpr(std::string tag, ACCExpr *next)
{
    bool hadWhile = next != nullptr;
    while (next) {
        printf("[%s:%d] %s value %s next %p param %p\n", __FUNCTION__, __LINE__, tag.c_str(), next->value.c_str(), next->next, next->param);
        for (auto item: next->operands)
            printf("[%s:%d] operand %s\n", __FUNCTION__, __LINE__, tree2str(item).c_str());
        if (next->param)
            dumpExpr(tag + "__PARAM", next->param);
        next = next->next;
    }
    if (hadWhile)
        printf("EEEEEEEEnd %s\n", tag.c_str());
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

static void expandExpression(ModuleIR *IR, ACCExpr *expr)
{
    if (isIdChar(expr->value[0]) && expr->operands.size()) {
        int size = -1;
        std::string subscript, post, fieldName = expr->value;
        ACCExpr *sub = expr->operands.front();
printf("[%s:%d] ZZZZZZ %p ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ\n", __FUNCTION__, __LINE__, sub);
        subscript = tree2str(sub->param);
        sub->operands.clear();
        expr->operands.pop_front();
        ACCExpr *next = expr->next;
        if (next && isIdChar(next->value[0])) {
            post = next->value;
            expr->next = next->next;
        }
        for (auto item: IR->fields)
            if (item.fldName == fieldName) {
                size = item.vecCount;
                break;
            }
printf("[%s:%d] ARRAAA size %d '%s' sub '%s' post '%s'\n", __FUNCTION__, __LINE__, size, fieldName.c_str(), subscript.c_str(), post.c_str());
        expr->value = fieldName + subscript + post;
        if (!isdigit(subscript[0])) {
            std::string ret = " ( ";
            for (int i = 0; i < size - 1; i++)
                ret += " ( " + subscript + " == " + autostr(i) + " ) ? "
                    + fieldName + autostr(i) + post + " : ";
            ret += fieldName + autostr(size - 1) + post + " ) ";
            ACCExpr *newTree = str2tree(ret);
            expr->value = newTree->value;
            expr->param = newTree->param;
        }
printf("[%s:%d] afterexpr %s\n", __FUNCTION__, __LINE__, tree2str(expr).c_str());
    }
    for (auto item: expr->operands)
        expandExpression(IR, item);
    if (expr->param)
        expandExpression(IR, expr->param);
    if (expr->next)
        expandExpression(IR, expr->next);
}

static ACCExpr *getExpression(ModuleIR *IR)
{
    std::string scanexp = scanExpression(bufp);
    bufp += scanexp.length();
    while (*bufp == ' ')
        bufp++;
    ACCExpr *expr = str2tree(scanexp);
    if (expr && expr->value == "(" && !expr->next) {
        expr = expr->param;
        //walkSubscript(expr);
    }
    if (expr)
        expandExpression(IR, expr);
    return expr;
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

static void walkName (MethodInfo *MI, ACCExpr *expr, ACCExpr *cond)
{
    if (isIdChar(expr->value[0]))
        if (!expr->next || expr->next->value != "{")
             MI->meta[MetaRead][expr->value].insert(tree2str(cond));
    for (auto item: expr->operands)
        walkName(MI, item, cond);
    if (expr->param)
        walkName(MI, expr->param, cond);
    if (expr->next)
        walkName(MI, expr->next, cond);
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
                auto insertRead = [&](ACCExpr *exprp, ACCExpr *cond) -> ACCExpr * {
                    if (!exprp)
                        return nullptr;
                    walkName(MI, exprp, cond);
                    expandExpression(IR, exprp);
                    return exprp;
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
                    MI->guard = insertRead(getExpression(IR), nullptr);
                IR->method[methodName] = MI;
                if (foundIf || (!foundParen && checkItem("if"))) {
                    std::string rdyName = getRdyName(methodName);
                    MethodInfo *MIRdy = new MethodInfo{nullptr};
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
                            ACCExpr *cond = insertRead(getExpression(IR), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *dest = getExpression(IR);
                            ParseCheck(checkItem("="), "store = missing");
                            ACCExpr *expr = insertRead(str2tree(bufp), cond);
                            MI->storeList.push_back(StoreListElement{dest, expr, cond});
                        }
                        else if (checkItem("LET")) {
                            std::string type = getToken();
                            ACCExpr *cond = insertRead(getExpression(IR), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *dest = getExpression(IR);
                            ParseCheck(checkItem("="), "store = missing");
                            ACCExpr *expr = insertRead(str2tree(bufp), cond);
                            MI->letList.push_back(LetListElement{dest, expr, cond, type});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            ACCExpr *cond = insertRead(getExpression(IR), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *expr = insertRead(str2tree(bufp), cond);
                            MI->callList.push_back(CallListElement{expr, cond, isAction});
                            std::string ee = tree2str(expr);
                            MI->meta[MetaInvoke][trimStr(ee.substr(0,ee.find("{")))].insert(tree2str(cond));
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
                MethodInfo *MIRdy = new MethodInfo{nullptr};
                MIRdy->rule = MI->rule;
                MIRdy->type = "INTEGER_1";
                MIRdy->guard = str2tree("1");
                IR->method[rdyName] = MIRdy;
            }
        }
    }
    for (auto irItem : irSeq)
         promoteGuards(irItem);
}
