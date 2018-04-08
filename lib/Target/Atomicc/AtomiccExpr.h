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
//#define NEWEXPR

#define MAX_EXPR_DEPTH 20

static std::string lexString;
static unsigned lexIndex;
static char lexChar;
static int trace_expr;// = 1;
static ACCExpr *repeatGet1Token;

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
    if (arg->infix) {
        std::string sep, op = arg->value;
        for (auto item: arg->operands) {
            ret += sep + tree2str(item);
            sep = " " + op + " ";
            if (op == "?")
                op = ":";
        }
    }
    else {
        ret += arg->value;
        for (auto item: arg->operands)
            ret += " " + tree2str(item);
    }
    ret += treePost(arg);
    if (arg->next)
        ret += " " + tree2str(arg->next);
    return ret;
}

static inline void dumpExpr(std::string tag, ACCExpr *next)
{
    while (next) {
        printf("DE: %s %p %s in %d next %p\n", tag.c_str(), next, next->value.c_str(), next->infix, next->next);
        int i = 0;
        for (auto item: next->operands) {
            dumpExpr(tag + "_" + autostr(i), item);
            i++;
        }
        next = next->next;
    }
}

static ACCExpr *allocExpr(std::string value, ACCExpr *arg = nullptr)
{
    ACCExpr *ret = new ACCExpr;
    ret->op = "";
    ret->value = value;
    ret->operands.clear();
    ret->next = nullptr;
    ret->infix = false;
    if (arg)
        ret->operands.push_back(arg);
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

static int findPrec(std::string s)
{
static struct {
    const char *op;
    int         prec;
} opPrec[] = {
    {"," , 1},

    {"?", 10}, {":", 10},

    {"&", 12}, {"|", 12},
    {"&&", 17}, {"||", 17},
    {"^", 18},

    {"==", 20}, {"!=" , 20}, {"<", 20}, {">", 20}, {"<=", 20}, {">=", 20},

    {"+", 30}, {"-", 30},
    {"*", 40}, {"%", 40},

    {nullptr, -1}};
    int ind = 0;
    while (opPrec[ind].op && opPrec[ind].op != s)
        ind++;
    if (s != "" && !opPrec[ind].op) {
        printf("[%s:%d] PPPPPPPPPPPP %s\n", __FUNCTION__, __LINE__, s.c_str());
        exit(-1);
    }
    return opPrec[ind].prec;
}

static ACCExpr *getExprList(ACCExpr *head, std::string terminator, bool parseState);
static ACCExpr *get1Token(void)
{
    std::string lexToken;
    auto getNext = [&] (void) -> void {
        lexToken += lexChar;
        lexChar = lexString[lexIndex++];
    };

    ACCExpr *ret = repeatGet1Token;
    repeatGet1Token = nullptr;
    if (ret)
        return ret;
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
    ret = allocExpr(lexToken);
//if (trace_expr) printf("[%s:%d] TOKEN: %p '%s'\n", __FUNCTION__, __LINE__, ret, lexToken.c_str());
    if (isParenChar(ret->value[0]))
        return getExprList(ret, treePost(ret).substr(1), false);
    return ret;
}

static bool checkOperand(std::string s)
{
    return isIdChar(s[0]) || isdigit(s[0]) || s == "(" || s == "{";
}
static bool checkOperator(std::string s)
{
    return s == "==" || s == "&" || s == "+" || s == "-" || s == "*" || s == "%" || s == "!="
      || s == "?" || s == ":" || s == "^" || s == ","
      || s == "|" || s == "||" || s == "<" || s == ">";
}

static ACCExpr *getExprList(ACCExpr *head, std::string terminator, bool operandHack)
{
static int indent;
if (trace_expr) printf("[%s:%d] ENTRY indent %d head %p termin %s state %d string '%s'\n", __FUNCTION__, __LINE__, ++indent, head, terminator.c_str(), operandHack, lexIndex < lexString.length() ? lexString.substr(lexIndex).c_str(): "NOSTRING");
if (trace_expr) dumpExpr("ENTRY", head);
    bool parseState = false;
    ACCExpr *currentOperand = nullptr;
    ACCExpr *tok;
    ACCExpr *exprStack[MAX_EXPR_DEPTH];
    int exprStackIndex = 0;
#define TOP exprStack[exprStackIndex]
    TOP = nullptr;
    if (head) {
        while ((tok = get1Token()) && tok->value != terminator) {
if (trace_expr) printf("[%s:%d] hack %d state %d tok [%p] %s currentOperand %p TOP %p\n", __FUNCTION__, __LINE__, operandHack, parseState, tok, tree2str(tok).c_str(), currentOperand, TOP);
            if ((parseState = !parseState)) {    /* Operand */
                ACCExpr *tnext = tok;
                if (operandHack)
                    tok = head;
                else
                    tnext = get1Token();
                operandHack = false;
                if (checkOperator(tok->value))
                    tok = allocExpr("(", tok);
                else if (!checkOperand(tok->value)) {
                    printf("[%s:%d] OPERAND CHECKFAILLLLLLLLLLLLLLL %s from %s\n", __FUNCTION__, __LINE__, tree2str(tok).c_str(), lexString.c_str());
                    exit(-1);
                }
                while (tnext && (tnext->value == "{" || tnext->value == "[" || isIdChar(tnext->value[0]))) {
                    assert(isIdChar(tok->value[0]));
                    tok->operands.push_back(tnext);
                    tnext = get1Token();
                }
                repeatGet1Token = tnext;
                currentOperand = tok;
            }
            else {                        /* Operator */
                std::string L = TOP ? TOP->value : "", R = tok->value;
                if (!checkOperator(R)) {
                    printf("[%s:%d] OPERATOR CHECKFAILLLLLLLLLLLLLLL %s from %s\n", __FUNCTION__, __LINE__, R.c_str(), lexString.c_str());
                    exit(-1);
                }
                else if (((L == R && L != "?") || (L == "?" && R == ":"))) 
{}
//printf("[%s:%d] EQL %s R %s\n", __FUNCTION__, __LINE__, L.c_str(), R.c_str());
else
{
                    if (TOP) {
                        int lprec = findPrec(L), rprec = findPrec(R);
                        if (lprec < rprec) {
                            exprStackIndex++;
                            TOP = nullptr;
                        }
                        else {
                            TOP->operands.push_back(currentOperand);
                            currentOperand = TOP;
                            while (exprStackIndex > 0 && lprec >= rprec) {
                                exprStackIndex--;
                                TOP->operands.push_back(currentOperand);
                                currentOperand = TOP;
                                L = TOP->value;
                                lprec = findPrec(L);
                            }
                        }
                    }
                    TOP = tok;
                    TOP->infix = true;
                }
                TOP->operands.push_back(currentOperand);
                currentOperand = nullptr;
            }
        }
        while (exprStackIndex != 0) {
            TOP->operands.push_back(currentOperand);
            currentOperand = TOP;
            exprStackIndex--;
        }
        if (currentOperand) {
            if (TOP)
                TOP->operands.push_back(currentOperand);
            else
                TOP = currentOperand;
        }
        if (TOP) {
            if (terminator != "")
                head->operands.push_back(TOP); // the first item in a recursed list
            else
                head = TOP;
        }
        if (head->value == "(" && head->operands.size() && head->operands.size() <= 1) {
            ACCExpr *next = head->next;
            head = head->operands.front();
            head->next = next;
        }
    }
if (trace_expr) printf("[%s:%d] indent %d RRRRRRRRRRREEEEEEETTTTTTTTTTTTT %p %s\n", __FUNCTION__, __LINE__, indent--, head, tree2str(head).c_str());
    return head;
}

static ACCExpr *str2tree(std::string arg)
{
    lexString = arg;
    lexIndex = 0;
    lexChar = lexString[lexIndex++];
    ACCExpr *head = getExprList(get1Token(), "", true);
    if (head && head->value == "(" && !head->next && head->operands.size())
        head = head->operands.front();
    return head;
}
