add_llvm_target(AtomiccCodeGen
  Atomicc.cpp
  AtomiccClone.cpp
  AtomiccGenerate.cpp
  AtomiccMap.cpp
  AtomiccMetaGen.cpp
  AtomiccPreprocess.cpp
  AtomiccRuntime.cpp
  AtomiccUtil.cpp
  AtomiccVerilog.cpp
  AtomiccIR.cpp
  )

add_subdirectory(TargetInfo)
