//===-- AtomiccExpr.h - Generating ACCExpr trees from strings -----===//
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

static std::string lexString;
static unsigned lexIndex;
static char lexChar;

static bool isIdChar(char ch)
{
    return isalpha(ch) || ch == '_' || ch == '$';
}

static bool isParenChar(char ch)
{
    return ch == '[' || ch == '(' || ch == '{';
}

static std::string treePost(ACCExpr *arg)
{
    if (arg->value == "[")
        return " ]";
    else if (arg->value == "(")
        return " )";
    else if (arg->value == "{")
        return " }";
    return "";
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

static ACCExpr *getExprList(ACCExpr *head);

static ACCExpr *get1Token(void)
{
    std::string lexToken;
    auto getNext = [&] (void) -> void {
        lexToken += lexChar;
        lexChar = lexString[lexIndex++];
    };

    while (lexChar == ' ' || lexChar == '\t')
        lexChar = lexString[lexIndex++];
    if(lexIndex > lexString.length() || lexChar == 0)
        return nullptr;
    if (isIdChar(lexChar))
        do {
            getNext();
        } while (isIdChar(lexChar) || isdigit(lexChar));
    else if (isdigit(lexChar))
        do {
            getNext();
        } while (isdigit(lexChar) || lexChar == '.');
    else if (lexChar == '+' || lexChar == '-' || lexChar == '*' || lexChar == '&' || lexChar == '|')
        do {
            getNext();
        } while (lexChar == lexToken[0]);
    else if (lexChar == '=' || lexChar == '<' || lexChar == '>' || lexChar == '!')
        do {
            getNext();
        } while (lexChar == '=' || lexChar == '<' || lexChar == '>');
    else if (isParenChar(lexChar) || lexChar == '/' || lexChar == '%'
        || lexChar == ']' || lexChar == '}' || lexChar == ')' || lexChar == '^'
        || lexChar == ',' || lexChar == '?' || lexChar == ':' || lexChar == ';')
        getNext();
    else {
        printf("[%s:%d] lexString '%s' unknown lexChar %c %x\n", __FUNCTION__, __LINE__, lexString.c_str(), lexChar, lexChar);
        exit(-1);
    }
    ACCExpr *ret = allocExpr(lexToken);
    if (isParenChar(ret->value[0]))
        return getExprList(ret);
    return ret;
}

static bool checkOperand(std::string s)
{
    return isIdChar(s[0]) || isdigit(s[0]) || s == "(" || s == "{";
}
static bool checkOperator(std::string s)
{
    return s == "{" || s == "[" 
      ||  s == "==" || s == "&" || s == "+" || s == "-" || s == "*" || s == "%" || s == "!="
      || s == "?" || s == ":" || s == "^" || s == ","
      || s == "|" || s == "||" || s == "<" || s == ">";
}

enum {ParseNone, ParseOperand, ParseOperator};
static ACCExpr *getExprList(ACCExpr *head)
{
    if (head) {
        std::string terminator = treePost(head);
    int parseState = (terminator != "" && !head->operands.size()) ? ParseOperand : ParseOperator;
        if (terminator.length() > 0)
            terminator = terminator.substr(1);
        ACCExpr *plist = head;
        while (1) {
            ACCExpr *tok = get1Token();
            if (!tok || tok->value == terminator)
                break;
            switch (parseState) {
            case ParseOperand:
                if (checkOperand(tok->value)) {
                    parseState = ParseOperator;
                    break;
                }
                printf("[%s:%d] OPERAND CHECKFAILLLLLLLLLLLLLLL %s from %s\n", __FUNCTION__, __LINE__, tok->value.c_str(), lexString.c_str());
                exit(-1);
                break;
            case ParseOperator:
                if (checkOperator(tok->value)) {
                    parseState = ParseOperand;
                    break;
                }
                printf("[%s:%d] OPERATOR CHECKFAILLLLLLLLLLLLLLL %s from %s\n", __FUNCTION__, __LINE__, tok->value.c_str(), lexString.c_str());
                exit(-1);
                break;
            }
            if (isIdChar(plist->value[0]) && isParenChar(tok->value[0]))
                plist->operands.push_back(tok);
            else {
                if (terminator != "" && !plist->operands.size() && isParenChar(plist->value[0]))
                    plist->operands.push_back(tok); // the first item in a recursed list
                else
                    plist->next = tok;
                plist = tok;
            }
        }
        if (head->value == "(" && head->operands.size() && !head->operands.front()->next) {
            ACCExpr *next = head->next;
            head = head->operands.front();
            head->next = next;
        }
    }
    return head;
}

static ACCExpr *str2tree(std::string arg)
{
    lexString = arg;
    lexIndex = 0;
    lexChar = lexString[lexIndex++];
    ACCExpr *head = getExprList(get1Token());
    if (head && head->value == "(" && !head->next && head->operands.size())
        head = head->operands.front();
    return head;
}
