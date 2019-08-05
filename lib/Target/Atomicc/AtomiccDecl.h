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
#include <list>
#include <set>
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/ExecutionEngine/Interpreter.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/Instructions.h"

#include "AtomiccIR.h"

#define MAX_BASIC_BLOCK_FLAGS 0x10
#define MAX_CHAR_BUFFER 1000
#define BOGUS_POINTER ((void *)0x5a5a5a5a5a5a5a5a)

#define ERRORIF(A) { \
      if(A) { \
          printf("[%s:%d]\n", __FUNCTION__, __LINE__); \
          exit(1); \
      }}

#define GIANT_SIZE 1024

typedef struct {
    int value;
    const char *name;
} INTMAP_TYPE;

typedef struct {
    std::string name;
    std::string options;
    std::string params;
    std::string templateOptions;
} FieldNameInfo;

typedef struct {
    std::string name;
    const Function *func;
} ClassMethodInfo;

class ClassMethodTable {
public:
    const StructType                  *STy;
    std::map<int, FieldNameInfo>      fieldName;
    std::list<ClassMethodInfo>        methods;
    std::map<int, const Type *>       replaceType;
    std::map<int, std::string>        replaceCount;
    std::list<std::string>            softwareName;
    std::map<std::string, bool>       ruleFunctions;
    ModuleIR* IR;
    ClassMethodTable() {}
};

typedef  struct {
    void *p;
    size_t size;
    Type *type;
    const StructType *STy;
    std::string vecCount;
} MEMORY_REGION;

typedef std::map<std::string, int> StringMapType;

extern ExecutionEngine *EE;
extern std::list<MEMORY_REGION> memoryRegion;
extern int trace_pair;
extern Module *globalMod;
extern std::map<std::string, Function *> functionMap;

void constructAddressMap(Module *Mod);
std::string printOperand(const Value *Operand);
std::string CBEMangle(const std::string &S);
void memdump(unsigned char *p, int len, const char *title);
void memdumpl(unsigned char *p, int len, const char *title);
const Metadata *fetchType(const Metadata *arg);
std::string ucName(std::string inname);
Instruction *cloneTree(const Instruction *I, Instruction *insertPoint);
void prepareClone(Instruction *TI, const Function *SourceF);
std::string printString(std::string arg);
std::string getMethodName(const Function *func);
const StructType *findThisArgument(const Function *func);
void preprocessModule(Module *Mod);
void prepareReplace(const Value *olda, Value *newa);
void recursiveDelete(Value *V);
void pushWork(ClassMethodTable *table, Function *func, std::string mName);
void dumpMemoryRegions(int arg);
ClassMethodTable *getClass(const StructType *STy);
bool isActionMethod(const Function *func);
bool isInterface(const StructType *STy);

void generateIR(std::string OutputDir);
int checkDerived(const Type *A, const Type *B);
const Function *getCallee(const Instruction *I);
std::string baseMethodName(std::string pname);
