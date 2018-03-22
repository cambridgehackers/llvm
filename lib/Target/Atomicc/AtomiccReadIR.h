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

static std::string lexString;
static int lexTotal;
static int lexIndex;
static char lexChar;

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

static std::string tree2str(ACCExpr *arg)
{
    std::string ret;
    if (!arg)
        return "";
    ret += arg->value;
    for (auto item: arg->operands)
        ret += " " + tree2str(item);
    ret += treePost(arg);
    if (arg->next)
        ret += " " + tree2str(arg->next);
    return ret;
}

static inline void dumpExpr(std::string tag, ACCExpr *next)
{
    bool hadWhile = next != nullptr;
    while (next) {
        printf("[%s:%d] %s value %s next %p\n", __FUNCTION__, __LINE__, tag.c_str(), next->value.c_str(), next->next);
        for (auto item: next->operands)
            printf("[%s:%d] operand %s\n", __FUNCTION__, __LINE__, tree2str(item).c_str());
        next = next->next;
    }
    if (hadWhile)
        printf("EEEEEEEEnd %s\n", tag.c_str());
}

static ACCExpr *allocExpr(std::string value)
{
    ACCExpr *ret = new ACCExpr;
    ret->op = "";
    ret->value = value;
    ret->operands.clear();
    ret->next = nullptr;
    return ret;
}

static ACCExpr *appendExpr(ACCExpr *prev, ACCExpr *next)
{
    while(prev->next)      // Skip to end of head list
        prev = prev->next;
    prev->next = next;     // Add on list to be appended
    while(prev->next)      // Skip to the end of total list
        prev = prev->next;
    return prev;           // Return pointer to last element in final list
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

static ACCExpr *get1Tokene(ACCExpr *prev, std::string terminator)
{
    ACCExpr *retptr = nullptr;
    TokenValue tok = get1Token();
    if (tok.type != TOK_EOF && tok.value != terminator) {
        ACCExpr *ret = allocExpr(tok.value), *plist = ret;
        retptr = ret;
        if (prev) {
            if (isIdChar(prev->value[0]) && ret->value == "[") {
                prev->operands.push_back(ret);
                retptr = prev;
            }
            else if (terminator != "" && !prev->operands.size()
             && (prev->value == "[" || prev->value == "(" || prev->value == "{"))
                prev->operands.push_back(ret); // the first item in a recursed list
            else
                prev->next = ret;
        }
        if (ret->value == "[" || ret->value == "(" || ret->value == "{")
            while ((plist = get1Tokene(plist, treePost(ret).substr(1))))
                ;
    }
    return retptr;
}

static ACCExpr *str2tree(std::string arg)
{
    lexString = arg;
    lexTotal = lexString.length();
    lexIndex = 0;
    lexChar = lexString[lexIndex++];
    ACCExpr *tok = get1Tokene(nullptr, "");
    ACCExpr *prev = tok;
    while ((prev = get1Tokene(prev, "")))
        ;
    if (tok && tok->value == "(" && !tok->next)
        tok = tok->operands.front();
    return tok;
}

static ACCExpr *getExpression(ModuleIR *IR)
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

static ACCExpr *walkRead (ModuleIR *IR, MethodInfo *MI, ACCExpr *expr, ACCExpr *cond)
{
    if (expr) {
        if (isIdChar(expr->value[0])) {
    if (expr->operands.size()) {
        int size = -1;
        std::string post, fieldName = expr->value;
        ACCExpr *sub = expr->operands.front();
        expr->operands.pop_front();
        std::string subscript = tree2str(sub->operands.front());
        sub->operands.clear();
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
            ACCExpr *next = expr->next, *newTree = str2tree(ret);
            expr->value = newTree->value;
            expr->next = newTree->next;
            expr->operands.clear();
            if (newTree->operands.size())
                expr->operands.push_back(newTree->operands.front());
            appendExpr(expr, next);
        }
    }
            if (MI && (!expr->next || expr->next->value != "{"))
                MI->meta[MetaRead][expr->value].insert(tree2str(cond));
        }
        for (auto item: expr->operands)
            walkRead(IR, MI, item, cond);
        if (expr->next)
            walkRead(IR, MI, expr->next, cond);
    }
    return expr;
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
                    MI->guard = walkRead(IR, MI, getExpression(IR), nullptr);
                IR->method[methodName] = MI;
                if (foundIf || (!foundOpenBrace && checkItem("if"))) {
                    MethodInfo *MIRdy = new MethodInfo{nullptr};
                    MIRdy->rule = MI->rule;
                    MIRdy->type = "INTEGER_1";
                    MIRdy->guard = walkRead(IR, nullptr, getExpression(IR), nullptr);
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
                            ACCExpr *cond = walkRead(IR, MI, getExpression(IR), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *dest = walkRead(IR, nullptr, getExpression(IR), nullptr);
                            ParseCheck(checkItem("="), "store = missing");
                            ACCExpr *expr = walkRead(IR, MI, str2tree(bufp), cond);
                            MI->storeList.push_back(StoreListElement{dest, expr, cond});
                        }
                        else if (checkItem("LET")) {
                            std::string type = getToken();
                            ACCExpr *cond = walkRead(IR, MI, getExpression(IR), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *dest = walkRead(IR, nullptr, getExpression(IR), nullptr);
                            ParseCheck(checkItem("="), "store = missing");
                            ACCExpr *expr = walkRead(IR, MI, str2tree(bufp), cond);
                            MI->letList.push_back(LetListElement{dest, expr, cond, type});
                        }
                        else if (checkItem("CALL")) {
                            bool isAction = checkItem("/Action");
                            ACCExpr *cond = walkRead(IR, MI, getExpression(IR), nullptr);
                            ParseCheck(checkItem(":"), "':' missing");
                            ACCExpr *expr = walkRead(IR, MI, str2tree(bufp), cond);
                            MI->callList.push_back(CallListElement{expr, cond, isAction});
                            if (isIdChar(expr->value[0]) && expr->next && expr->next->value == "{")
                                MI->meta[MetaInvoke][expr->value].insert(tree2str(cond));
                            else {
                                printf("[%s:%d] called method name not found %s\n", __FUNCTION__, __LINE__, tree2str(expr).c_str());
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
