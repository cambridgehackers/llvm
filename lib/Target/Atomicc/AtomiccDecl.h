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
#include "llvm/ADT/StringExtras.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/ExecutionEngine/Interpreter.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/Instructions.h"

#define MODULE_SEPARATOR "$"

#define MAX_BASIC_BLOCK_FLAGS 0x10
#define MAX_CHAR_BUFFER 1000
#define BOGUS_POINTER ((void *)0x5a5a5a5a5a5a5a5a)

#define ERRORIF(A) { \
      if(A) { \
          printf("[%s:%d]\n", __FUNCTION__, __LINE__); \
          exit(1); \
      }}

#define GIANT_SIZE 1024

enum {ProcessNone=0, ProcessVerilog, ProcessCPP};
enum {MetaNone, MetaRead, MetaWrite, MetaInvoke, MetaMax};

typedef struct {
    int value;
    const char *name;
} INTMAP_TYPE;

typedef struct {
    std::string target;
    std::string source;
    const StructType *STy;
} InterfaceConnectType;

typedef struct {
    BasicBlock *bb;
    std::string value;
} MuxValueEntry;

typedef struct {
    BasicBlock *bb;
    std::string signal;
} MuxEnableEntry;

typedef std::map<std::string,std::list<Value *>> MetaRef;
typedef struct {
    MetaRef list[MetaMax];
} MetaData;

class ClassMethodTable {
public:
    const StructType                  *STy;
    std::map<std::string, Function *> method;
    std::map<int, Type *>             replaceType;
    std::map<int, uint64_t>           replaceCount;
    std::map<int, bool>               allocateLocally;
    std::map<std::string, Function *> ruleFunctions;
    std::list<InterfaceConnectType>   interfaceConnect;
    std::string                       instance;
    std::list<std::string>            metaList;
    std::map<const Function *, std::string> guard;
    std::map<std::string, std::string> priority; // indexed by rulename, result is 'high'/etc
// 'Or' together ENA lines from all invocations of a method from this class
    std::list<MuxEnableEntry> muxEnableList;
// 'Mux' together parameter settings from all invocations of a method from this class
    std::map<std::string, std::list<MuxValueEntry>> muxValueList;
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
extern std::map<const StructType *,ClassMethodTable *> classCreate;
extern std::map<Function *, Function *> ruleRDYFunction;
extern std::map<Function *, Function *> ruleENAFunction;
extern std::map<const Function *, std::string> pushSeen;
extern std::list<MEMORY_REGION> memoryRegion;
extern std::list<Function *> fixupFuncList;
extern int trace_pair;
extern Module *globalMod;
extern std::map<const Function *, MetaData> funcMetaMap;
extern std::map<const Function *,std::list<StoreInst *>> storeList;
extern std::map<const Function *,std::list<Instruction *>> functionList;
extern std::map<const Function *,std::list<Instruction *>> callList;
extern std::map<const Function *,std::list<Instruction *>> declareList;

int validateAddress(int arg, void *p);
void constructAddressMap(Module *Mod);
std::string fieldName(const StructType *STy, uint64_t ind);
std::string printType(Type *Ty, bool isSigned, std::string NameSoFar, std::string prefix, std::string postfix, bool ptr);
std::string printOperand(Value *Operand, bool Indirect);
std::string getStructName(const StructType *STy);
std::string CBEMangle(const std::string &S);
std::string verilogArrRange(Type *Ty);
void memdump(unsigned char *p, int len, const char *title);
void memdumpl(unsigned char *p, int len, const char *title);
bool GenerateRunOnModule(Module *Mod, std::string OutDirectory);
const Metadata *fetchType(const Metadata *arg);
std::string ucName(std::string inname);
Instruction *cloneTree(const Instruction *I, Instruction *insertPoint);
void prepareClone(Instruction *TI, const Function *SourceF);
std::string printString(std::string arg);
std::string getMethodName(std::string name);
bool endswith(std::string str, std::string suffix);
void generateClassDef(const StructType *STy, FILE *OStr, FILE *OHdr);
void generateModuleDef(const StructType *STy, FILE *OStr);
const StructType *findThisArgument(Function *func);
void preprocessModule(Module *Mod);
std::string GetValueName(const Value *Operand);
Value *getCondition(BasicBlock *bb, int invert);
int64_t getGEPOffset(VectorType **LastIndexIsVector, gep_type_iterator I, gep_type_iterator E);
void prepareReplace(const Value *olda, Value *newa);
void setCondition(BasicBlock *bb, int invert, Value *val);
void recursiveDelete(Value *V);
void setSeen(Function *func, std::string mName);
void dumpMemoryRegions(int arg);
void generateContainedStructs(const StructType *STy, FILE *OStrV, FILE *OStrVH, FILE *OStrC, FILE *OStrCH);
void metaGenerate(const StructType *STy, FILE *OStr);
bool isActionMethod(const Function *func);
void getClass(const StructType *STy);
void buildPrefix(ClassMethodTable *table);
std::string printCall(Instruction *I);
bool isAlloca(Value *arg);
bool isInterface(const StructType *STy);
