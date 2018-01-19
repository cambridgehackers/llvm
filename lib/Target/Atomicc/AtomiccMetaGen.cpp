//===-- AtomiccMetaGen.cpp - Generating Verilog from LLVM -----===//
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
#include "llvm/IR/Instructions.h"

using namespace llvm;

#include "AtomiccDecl.h"

void metaGenerate(ModuleIR *IR, FILE *OStr)
{
    std::map<std::string, int> exclusiveSeen;
    std::list<std::string>     metaList;
    // write out metadata comments at end of the file
    metaList.push_front("//METASTART; " + IR->name);
    for (auto item: IR->fields) {
        int64_t vecCount = item.vecCount;
        int dimIndex = 0;
        if (item.iIR)
        do {
            std::string fldName = item.fldName;
            if (vecCount != -1)
                fldName += utostr(dimIndex++);
            if (item.isPtr)
                metaList.push_back("//METAEXTERNAL; " + fldName + "; " + item.iIR->name + ";");
            else if (item.iIR->name.substr(0,12) != "l_struct_OC_"
                 && item.iIR->name.substr(0,12) != "l_ainterface")
                metaList.push_back("//METAINTERNAL; " + fldName + "; " + item.iIR->name + ";");
        } while(vecCount-- > 0);
    }
    for (auto FI : IR->method) {
        std::string methodName = FI.first;
        std::string temp = IR->method[methodName]->guard;
        if (endswith(methodName, "__RDY"))
            metaList.push_back("//METAGUARD; "
                + methodName.substr(0, methodName.length()-5) + "; " + temp + ";");
        else if (endswith(methodName, "__READY"))
            metaList.push_back("//METAGUARDV; "
                + methodName.substr(0, methodName.length()-7) + "; " + temp + ";");
        else {
            // For each method/rule of the current class,
            // gather up metadata generated by processFunction
            MetaData *bm = &IR->method[methodName]->meta;
            std::string temp;
            for (auto titem: bm->list[MetaInvoke])
                for (auto item: titem.second)
                    temp += item + ":" + titem.first + ";";
            if (temp != "")
                metaList.push_back("//METAINVOKE; " + methodName + "; " + temp);
            std::map<std::string,std::string> metaBefore;
            std::map<std::string,std::string> metaConflict;
            for (auto innerFI : IR->method) {
                std::string innermethodName = innerFI.first;
                MetaData *innerbm = &IR->method[innermethodName]->meta;
                std::string tempConflict;
                if (innermethodName == methodName)
                    continue;
                // scan all other rule/methods of this class
                for (auto inneritem: innerbm->list[MetaWrite]) {
                    for (auto item: bm->list[MetaRead])
                        // if the current method reads a state element that
                        // is written by another method, add it to the 'before' list
                        if (item.first == inneritem.first) {
//printf("[%s:%d] before conflict '%s' innerunc %s methodName %s\n", __FUNCTION__, __LINE__, item.first.c_str(), innerFI.first.c_str(), methodName.c_str());
                            metaBefore[innermethodName] = "; :";
                            break;
                        }
                    for (auto item: bm->list[MetaWrite])
                        // if the current method writes a state element that
                        // is written by another method, add it to the 'conflict' list
                        if (item.first == inneritem.first) {
                            metaConflict[innermethodName] = "; ";
                            break;
                        }
                }
                for (auto inneritem: innerbm->list[MetaInvoke]) {
                    for (auto item: bm->list[MetaInvoke])
                        if (item.first == inneritem.first) {
//printf("[%s:%d] conflict methodName %s innermethodName %s item %s\n", __FUNCTION__, __LINE__, methodName.c_str(), innermethodName.c_str(), item.first.c_str());
                            metaConflict[innermethodName] = "; ";
                            break;
                        }
                }
            }
            std::string metaStr;
            for (auto item: metaConflict)
                 if (item.second != "" && !exclusiveSeen[item.first])
                     metaStr += item.second + item.first;
            exclusiveSeen[methodName] = 1;
            if (metaStr != "")
                metaList.push_back("//METAEXCLUSIVE; " + methodName + metaStr);
            metaStr = "";
            for (auto item: metaBefore)
                 if (item.second != "")
                     metaStr += item.second + item.first;
            if (metaStr != "")
                metaList.push_back("//METABEFORE; " + methodName + metaStr);
        }
    }
    std::string ruleNames;
    for (auto item : IR->ruleFunctions)
        if (item.second)
            ruleNames += "; " + item.first;
    if (ruleNames != "")
        metaList.push_back("//METARULES" + ruleNames);
    for (auto item: IR->interfaceConnect) {
        std::string tname = item.target;
        std::string sname = item.source;
printf("[%s:%d] METACONNECT %s %s\n", __FUNCTION__, __LINE__, tname.c_str(), sname.c_str());
        for (auto mitem: item.IR->method)
            metaList.push_back("//METACONNECT; " + tname + MODULE_SEPARATOR + mitem.first
                                              + "; " + sname + MODULE_SEPARATOR + mitem.first);
    }
    for (auto item : IR->priority)
        metaList.push_back("//METAPRIORITY; " + item.first + "; " + item.second);
    for (auto item : metaList)
        fprintf(OStr, "%s\n", item.c_str());
}
