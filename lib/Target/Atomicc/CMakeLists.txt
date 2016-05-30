add_llvm_target(AtomiccCodeGen
  Atomicc.cpp
  AtomiccClone.cpp
  AtomiccCpp.cpp
  AtomiccGenerate.cpp
  AtomiccMain.cpp
  AtomiccMap.cpp
  AtomiccMetaGen.cpp
  AtomiccPreprocess.cpp
  AtomiccRuntime.cpp
  AtomiccUtil.cpp
  AtomiccVerilog.cpp
  )

add_subdirectory(TargetInfo)
