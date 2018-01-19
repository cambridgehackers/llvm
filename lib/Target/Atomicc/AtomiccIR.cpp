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
 * Generate Module info into IR
 */
void generateModuleIR(ModuleIR *IR, const StructType *STy)
{
    ClassMethodTable *table = getClass(STy);

    for (auto FI : table->method) {
        std::string methodName = FI.first;
        const Function *func = FI.second;
        MethodInfo *MI = new MethodInfo{""};
        IR->method[methodName] = MI;
        if (!IR->ruleFunctions[methodName.substr(0, methodName.length()-5)]) {
            MI->retArrRange = verilogArrRange(func->getReturnType());
            MI->action = isActionMethod(func);
            auto AI = func->arg_begin(), AE = func->arg_end();
            for (AI++; AI != AE; ++AI)
                MI->params.push_back(ParamElement{verilogArrRange(AI->getType()), AI->getName()});
        }
    }
    // generate local state element declarations
    int Idx = 0;
    for (auto I = STy->element_begin(), E = STy->element_end(); I != E; ++I, Idx++) {
        std::string fldName = fieldName(STy, Idx);
        const Type *element = *I;
        int64_t vecCount = -1;
        int dimIndex = 0;
        if (const Type *newType = table->replaceType[Idx]) {
            element = newType;
            vecCount = IR->replaceCount[Idx];
        }
        if (fldName == "")
            continue;
        if (const PointerType *PTy = dyn_cast<PointerType>(element))
        if (const StructType *iSTy = dyn_cast<StructType>(PTy->getElementType()))
        if (isInterface(iSTy))
            IR->outcall.push_back(OutcallInterface{fldName, getClass(iSTy)->IR});
        if (const StructType *STy = dyn_cast<StructType>(element))
            IR->fields.push_back(FieldElement{fldName, vecCount, verilogArrRange(element), getClass(STy)->IR, "", false});
        else if (const PointerType *PTy = dyn_cast<PointerType>(element)) {
            if (const StructType *STy = dyn_cast<StructType>(PTy->getElementType()))
                IR->fields.push_back(FieldElement{fldName, vecCount, verilogArrRange(element), getClass(STy)->IR, "", true});
        }
        else
            IR->fields.push_back(FieldElement{fldName, vecCount, "", nullptr, printType(element, false, "@", "", "", false), false});
    }
}
