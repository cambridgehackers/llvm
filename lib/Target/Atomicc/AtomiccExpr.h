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
static int lexTotal;
static int lexIndex;
static char lexChar;

bool isIdChar(char ch)
{
    return isalpha(ch) || ch == '_' || ch == '$';
}

bool isParenChar(char ch)
{
    return ch == '[' || ch == '(' || ch == '{';
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

static ACCExpr *get1Token(ACCExpr *prev, std::string terminator)
{
    std::string lexToken;
    auto getNext = [&] (void) -> void {
        lexToken += lexChar;
        lexChar = lexString[lexIndex++];
    };

    while (lexChar == ' ' || lexChar == '\t')
        lexChar = lexString[lexIndex++];
    if(lexIndex > lexTotal || lexChar == 0)
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
    if (lexToken == terminator)
        return nullptr;
    ACCExpr *ret = allocExpr(lexToken), *plist = ret, *retptr = ret;
    if (prev) {
        if (isIdChar(prev->value[0]) && ret->value == "[") {
            prev->operands.push_back(ret);
            retptr = prev;
        }
        else if (terminator != "" && !prev->operands.size() && isParenChar(prev->value[0]))
            prev->operands.push_back(ret); // the first item in a recursed list
        else
            prev->next = ret;
    }
    if (isParenChar(ret->value[0]))
        while ((plist = get1Token(plist, treePost(ret).substr(1))))
            ;
    return retptr;
}

static ACCExpr *str2tree(std::string arg)
{
    lexString = arg;
    lexTotal = lexString.length();
    lexIndex = 0;
    lexChar = lexString[lexIndex++];
    ACCExpr *tok = get1Token(nullptr, ""), *prev = tok;
    while ((prev = get1Token(prev, "")))
        ;
    if (tok && tok->value == "(" && !tok->next)
        tok = tok->operands.front();
    return tok;
}
