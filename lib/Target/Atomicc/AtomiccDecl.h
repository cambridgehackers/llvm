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
    std::string fname;
    Function   *func;
} FuncInfo;

class ClassMethodTable {
public:
    const StructType                  *STy;
    std::map<int, std::string>        fieldName;
    std::map<std::string, const Function *> method;
    std::map<int, const Type *>       replaceType;
    std::map<int, uint64_t>           replaceCount;
    std::map<std::string, FuncInfo>   funcMap;
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
    uint64_t   vecCount;
} MEMORY_REGION;

typedef std::map<std::string, int> StringMapType;

extern ExecutionEngine *EE;
extern std::map<const Function *, Function *> ruleRDYFunction;
extern std::list<MEMORY_REGION> memoryRegion;
extern int trace_pair;
extern Module *globalMod;

void constructAddressMap(Module *Mod);
std::string fieldName(const StructType *STy, uint64_t ind);
std::string printOperand(const Value *Operand, bool Indirect);
std::string getStructName(const StructType *STy);
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
std::string GetValueName(const Value *Operand);
int64_t getGEPOffset(VectorType **LastIndexIsVector, gep_type_iterator I, gep_type_iterator E);
void prepareReplace(const Value *olda, Value *newa);
void recursiveDelete(Value *V);
void pushPair(Function *enaFunc, std::string enaName, Function *rdyFunc, std::string rdyName);
void dumpMemoryRegions(int arg);
ClassMethodTable *getClass(const StructType *STy);
bool isActionMethod(const Function *func);
bool isInterface(const StructType *STy);

void generateIR(std::string OutputDir);
void generateVerilog(std::string OutputDir);
void readModuleIR(std::list<ModuleIR *> &irSeq, FILE *OStr);
void metaGenerate(ModuleIR *IR, FILE *OStr);
void generateModuleDef(ModuleIR *IR, FILE *OStr);
