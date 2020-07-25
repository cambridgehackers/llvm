add_llvm_target(AtomiccCodeGen
  Atomicc.cpp
  AtomiccGenerate.cpp
  AtomiccMap.cpp
  AtomiccPreprocess.cpp
  AtomiccRuntime.cpp
  AtomiccUtil.cpp
  )

add_subdirectory(TargetInfo)
