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
#include <stdio.h>
#include "llvm/IR/Instructions.h"
#include "llvm/ADT/StringExtras.h"

using namespace llvm;

#include "AtomiccDecl.h"


static uint64_t sizeType(const Type *Ty)
{
    //const DataLayout *TD = EE->getDataLayout();
    switch (Ty->getTypeID()) {
    case Type::IntegerTyID:
        return cast<IntegerType>(Ty)->getBitWidth();
    case Type::StructTyID: {
        //unsigned NumBits = TD->getTypeAllocSize(Ty) * 8;
        const StructType *STy = cast<StructType>(Ty);
        uint64_t len = 0;
        int Idx = 0;
        for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
            if (fieldName(STy, Idx) != "")
                len += sizeType(*I);
        }
        return len;
        }
    case Type::ArrayTyID: {
        const ArrayType *ATy = cast<ArrayType>(Ty);
        unsigned len = ATy->getNumElements();
        if (len == 0) len = 1;
        return len * sizeType(ATy->getElementType());
        }
    case Type::PointerTyID:
        return sizeType(cast<PointerType>(Ty)->getElementType());
    case Type::VoidTyID:
        return 0;
    case Type::FunctionTyID:
    default:
        llvm_unreachable("Unhandled case in sizeType!");
    }
}

std::string verilogArrRange(const Type *Ty)
{
    uint64_t NumBits = sizeType(Ty);

    if (NumBits > 1)
        return "[" + utostr(NumBits - 1) + ":0]";
    return "";
}

/*
 * Generate verilog module header for class definition or reference
 */
static void generateModuleSignature(const StructType *STy, std::string instance)
{
    ClassMethodTable *table = getClass(STy);
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        std::string fldName = fieldName(STy, Idx);
        const Type *element = *I;
        if (const Type *newType = table->replaceType[Idx])
            element = newType;
        const PointerType *PTy = dyn_cast<PointerType>(element);
        if (fldName == "" || !PTy)
            continue;
        const StructType *iSTy = dyn_cast<StructType>(PTy->getElementType());
        if (isInterface(iSTy))
            table->IR->outcall[instance].push_back(OutcallInterface{fldName + MODULE_SEPARATOR, getClass(iSTy)->IR});
    }
}

static std::string cleanupValue(std::string arg)
{
    int ind;
    while((ind = arg.find("{}")) > 0)
        arg = arg.substr(0, ind) + arg.substr(ind+2); // remove '{}'
    return arg;
}

/*
 * Generate Module info into IR
 */
void generateModuleIR(ModuleIR *IR, const StructType *STy)
{
    std::list<std::string> alwaysLines, resetList;
    ClassMethodTable *table = IR->table;
    for (auto FI : IR->method) {
        FI.second->guard = cleanupValue(FI.second->guard);
    }

    generateModuleSignature(STy, "");
    // generate local state element declarations
    // generate wires for internal methods RDY/ENA.  Collect state element assignments
    // from each method
    for (auto FI : table->method) {
        std::string methodName = FI.first;
        MethodInfo *MI = table->IR->method[methodName];
        std::string rdyName = methodName.substr(0, methodName.length()-5) + "__RDY";
        if (endswith(methodName, "__VALID"))
            rdyName = methodName.substr(0, methodName.length()-7) + "__READY";
        for (auto info: MI->callList) {
            std::string tempCond = methodName + "_internal" + info.cond;
            std::string rval = info.value; // get call info
            int ind = rval.find("{");
            std::string calledName = rval.substr(0, ind);
            rval = rval.substr(ind+1);
            rval = cleanupValue(rval.substr(0, rval.length()-1));
            //if (info.isAction)
                //muxEnableList.push_back(MuxEnableEntry{tempCond, calledName});
            while(rval.length()) {
                std::string rest;
                int ind = rval.find(",");
                if (ind > 0) {
                    rest = rval.substr(ind+1);
                    rval = rval.substr(0, ind);
                }
                ind = rval.find(";");
                std::string paramValue;
                if (ind > 0) {
                    paramValue = rval.substr(ind+1);
                    rval = rval.substr(0, ind);
                }
                //muxValueList[rval].push_back(MuxValueEntry{tempCond, paramValue});
                rval = rest;
            }
        }
    }
    // generate local state element declarations
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        const Type *element = *I;
        int64_t vecCount = -1;
        int dimIndex = 0;
        std::string vecDim;
        if (const Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = table->IR->replaceCount[Idx];
        }
        do {
        std::string fldName = fieldName(STy, Idx);
        if (fldName != "") {
            if (vecCount != -1)
                fldName += utostr(dimIndex++);
            if (const StructType *STy = dyn_cast<StructType>(element)) {
                std::string structName = getStructName(STy);
                if (structName.substr(0,12) == "l_struct_OC_") {
                    IR->fields.push_back(FieldElement{fldName, vecCount, structName, verilogArrRange(element), nullptr, ""});
                    //fprintf(OStr, "    reg%s %s;\n", verilogArrRange(element).c_str(), fldName.c_str());
                    //resetList.push_back(fldName);
                }
                else if (!isInterface(STy)) {
                    IR->fields.push_back(FieldElement{fldName, vecCount, structName, "", getClass(STy)->IR, ""});
                    generateModuleSignature(STy, fldName);
                }
            }
            else if (!dyn_cast<PointerType>(element)) {
                IR->fields.push_back(FieldElement{fldName, vecCount, "", "", nullptr, printType(element, false, fldName, "", "", false)});
                //fprintf(OStr, "    %s;\n", printType(element, false, fldName, "", "", false).c_str());
                //resetList.push_back(fldName);
            }
        }
        } while(vecCount-- > 0);
    }
}
