cmake_minimum_required(VERSION 3.16)
project(tfhe++ CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS
    "-march=native -O3 -g -flto -funroll-loops -Wall -Wextra -pedantic -Wno-sign-compare"
)

option(USE_RANDEN "Use randen as CSPRNG" ON)
option(USE_80BIT_SECURITY "Use 80bit security parameter(faster)" OFF)
option(USE_CGGI19 "Use the parameter set proposed in CGGI19" OFF)
option(USE_CONCRETE "Use the parameter set proposed in CONCRETE" OFF)
option(USE_TFHE_RS "Use the parameter set proposed in TFHE-rs" OFF)
option(USE_TERNARY "Use ternary secret keys" OFF)
option(USE_TERNARY_CMUX "Use ternary cmux" OFF)
option(USE_KEY_BUNDLE "Use key bundle algorithm" OFF)

option(USE_AVX512 "Use AVX512 ver. SPQLIOS" OFF)
option(USE_MKL "Use Intel MKL" OFF)
option(USE_FFTW3 "Use FFTW3" OFF)
option(USE_SPQLIOX_AARCH64 "Use spqliox_aarch64" OFF)
option(USE_HEXL "Use Intel HEXL" OFF)

option(ENABLE_TEST "Build tests" OFF)
option(ENABLE_BENCHMARK "Build benchmarks" OFF)
option(ENABLE_TUTORIAL "Build tutorial" OFF)
option(USE_PERF "Use Google Profiler" OFF)

option(ENABLE_SHARED "Build as shared libraries" OFF)

if(USE_RANDEN)
  add_compile_definitions(USE_RANDEN)
endif()

if(USE_80BIT_SECURITY)
  add_compile_definitions(USE_80BIT_SECURITY)
elseif(USE_CGGI19)
  add_compile_definitions(USE_CGGI19)
elseif(USE_CONCRETE)
  add_compile_definitions(USE_CONCRETE)
elseif(USE_TFHE_RS)
  add_compile_definitions(USE_TFHE_RS)
elseif(USE_TERNARY_CMUX)
  add_compile_definitions(USE_TERNARY)
  add_compile_definitions(USE_TERNARY_CMUX)
elseif(USE_TERNARY)
  add_compile_definitions(USE_TERNARY)
endif()

if(NOT USE_TERNARY)
  if(USE_KEY_BUNDLE)
    add_compile_definitions(USE_KEY_BUNDLE)
  endif()
endif()

if(USE_MKL)
  set(USE_FFTW3 ON)
endif()

if(USE_AVX512)
  string(APPEND CMAKE_CXX_FLAGS " -mprefer-vector-width=512")
endif()

if(USE_FFTW3)
  add_compile_definitions(USE_FFTW3)
  add_subdirectory(thirdparties/fftw)
elseif(USE_SPQLIOX_AARCH64)
  add_compile_definitions(USE_SPQLIOX_AARCH64)
  add_subdirectory(thirdparties/spqliox_aarch64)
else()
  add_subdirectory(thirdparties/spqlios)
endif()

if(USE_HEXL)
  add_compile_definitions(USE_HEXL)
  add_subdirectory(thirdparties/hexl)
  # set(CMAKE_CXX_FLAGS "-march=native -O3 -g -funroll-loops -Wall -Wextra
  # -pedantic -Wno-sign-compare -mprefer-vector-width=512" )
endif()

# For OpenMP
find_package(OpenMP)
if(OpenMP_FOUND)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
endif()

if(USE_RANDEN)
  add_subdirectory(thirdparties/randen)
endif()
add_subdirectory(src)

if(ENABLE_TEST)
  add_subdirectory(test)
endif()
if(ENABLE_BENCHMARK)
  add_subdirectory(benchmark)
endif()
if(ENABLE_TUTORIAL)
  add_subdirectory(tutorial)
endif()

install(TARGETS tfhe++ LIBRARY DESTINATION lib)
