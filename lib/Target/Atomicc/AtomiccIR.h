/* Copyright (c) 2015 The Connectal Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
#ifndef __ATOMICIR_H__
#define __ATOMICIR_H__
#include <stdio.h>
#include <string>
#include <list>
#include <set>
#include <map>

#define MODULE_SEPARATOR "$"

#define MAX_READ_LINE 10240

static inline std::string autostr(uint64_t X, bool isNeg = false) {
  char Buffer[21];
  char *BufPtr = std::end(Buffer);

  if (X == 0) *--BufPtr = '0';  // Handle special case...

  while (X) {
    *--BufPtr = '0' + char(X % 10);
    X /= 10;
  }

  if (isNeg) *--BufPtr = '-';   // Add negative sign...
  return std::string(BufPtr, std::end(Buffer));
}

static bool inline endswith(std::string str, std::string suffix)
{
    int skipl = str.length() - suffix.length();
    return skipl >= 0 && str.substr(skipl) == suffix;
}
static bool inline startswith(std::string str, std::string suffix)
{
    return str.substr(0, suffix.length()) == suffix;
}

typedef struct ACCExpr {
    std::list<ACCExpr *>operands;
    std::string value;
} ACCExpr;

typedef struct {
    std::string target;
    std::string source;
    std::string type;
    bool        isForward;
} InterfaceConnectType;

enum {MetaNone, MetaRead, MetaInvoke, MetaMax};

typedef std::set<std::string> MetaSet;
typedef std::map<std::string,MetaSet> MetaRef;

typedef struct {
    ACCExpr *dest;
    ACCExpr *value;
    ACCExpr *cond;
} StoreListElement;

typedef struct {
    ACCExpr *dest;
    ACCExpr *value;
    ACCExpr *cond;
    std::string type;
} LetListElement;

typedef struct {
    ACCExpr *value;
    ACCExpr *cond;
    bool isAction;
} CallListElement;

typedef struct {
    std::string name;
    std::string type;
} ParamElement;

typedef struct {
    std::string name;
    std::string type;
} UnionItem;

typedef struct {
    std::string type;
    bool        noReplace;
} AllocaItem;

typedef struct {
    ACCExpr *cond;
    std::string var;
    ACCExpr *init;
    ACCExpr *limit;
    ACCExpr *incr;
    std::string body;
} GenerateForItem;

typedef struct {
    ACCExpr                   *guard;
    std::string                name;
    bool                       rule;
    bool                       action;
    std::list<StoreListElement *> storeList;
    std::list<LetListElement *> letList;
    std::list<CallListElement *> callList;
    std::list<CallListElement *> printfList;
    std::string                type;
    std::list<ParamElement>    params;
    std::list<GenerateForItem> generateFor;
    std::map<std::string, AllocaItem> alloca;
    MetaRef                    meta[MetaMax];
} MethodInfo;

typedef struct {
    std::string fldName;
    int64_t     vecCount;
    std::string type;
    bool        isPtr;
    bool        isInput; // used for verilog interfaces
    bool        isOutput; // used for verilog interfaces
    bool        isInout; // used for verilog interfaces
    bool        isParameter; // used for verilog interfaces
    bool        isShared;    // used for __shared (common CSE) support
    bool        isLocalInterface; // interface declaration that is used to connect to local objects (does not appear in module signature)
} FieldElement;

typedef struct ModuleIR {
    std::string                       name;
    std::list<std::string>            metaList;
    std::list<std::string>            softwareName;
    std::map<std::string, MethodInfo *> method;
    std::map<std::string, MethodInfo *> generateBody;
    std::map<std::string, std::string> priority; // indexed by rulename, result is 'high'/etc
    std::list<FieldElement>           fields;
    std::map<std::string, std::string> params;
    std::list<UnionItem>              unionList;
    std::list<FieldElement>           interfaces;
    std::list<InterfaceConnectType>   interfaceConnect;
    int                               genvarCount;
    bool                              isInterface;
} ModuleIR;
#endif /* __ATOMICIR_H__ */
