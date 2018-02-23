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

#define MAX_READ_LINE 1024

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

static std::string inline cleanupValue(std::string arg)
{
    int ind;
    while((ind = arg.find("{}")) > 0)
        arg = arg.substr(0, ind) + arg.substr(ind+2); // remove '{}'
    return arg;
}

typedef struct {
    std::string target;
    std::string source;
    struct ModuleIR *IR;
} InterfaceConnectType;

enum {MetaNone, MetaRead, MetaInvoke, MetaMax};

typedef std::map<std::string,std::set<std::string>> MetaRef;

typedef struct {
    std::string dest;
    std::string value;
    std::string cond;
    bool        isAlloca;
} StoreListElement;

typedef struct {
    std::string value;
    std::string cond;
    bool isAction;
} CallListElement;

typedef struct {
    std::string name;
    std::string type;
} ParamElement;

typedef struct {
    std::string                guard;
    bool                       rule;
    std::list<StoreListElement> storeList;
    std::list<CallListElement> callList;
    std::string                type;
    std::list<ParamElement>    params;
    std::map<std::string, std::string> alloca;
    MetaRef                    meta[MetaMax];
} MethodInfo;

typedef struct {
    std::string      fldName;
    struct ModuleIR *IR;
} OutcallInterface;

typedef struct {
    std::string fldName;
    int64_t     vecCount;
    std::string type;
    struct ModuleIR *IR;
    unsigned    arrayLen;
    bool        isPtr;
} FieldElement;

typedef struct ModuleIR {
    std::string                       name;
    std::list<std::string>            metaList;
    std::list<std::string>            softwareName;
    std::map<std::string, MethodInfo *> method;
    std::list<OutcallInterface>       outcall;
    std::map<std::string, std::string> priority; // indexed by rulename, result is 'high'/etc
    std::list<FieldElement>           fields;
    std::list<FieldElement>           interfaces;
    std::list<InterfaceConnectType>   interfaceConnect;
} ModuleIR;

void readModuleIR(std::list<ModuleIR *> &irSeq, FILE *OStr);
void promoteGuards(ModuleIR *arg);
std::string getRdyName(std::string basename);
std::string scanExpression(const char *val);
#endif /* __ATOMICIR_H__ */
