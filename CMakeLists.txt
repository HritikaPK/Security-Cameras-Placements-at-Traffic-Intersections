cmake_minimum_required(VERSION 2.8.12)
project(ece650-prj)

if (EXISTS "${CMAKE_SOURCE_DIR}/minisat")
  add_subdirectory(minisat)
else()
  message (FATAL_ERROR "MiniSat not found. Use `git clone https://git.uwaterloo.ca/ece650-f23/minisat.git` to check it out.")
endif()


## ECE650 Specific configuration start here
## Project specific configurations go here

# enable c++11 support
set (CMAKE_CXX_FLAGS "-std=c++11 -Wall ${CMAKE_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS -pthread)
# expose minisat header files
include_directories(${CMAKE_SOURCE_DIR}/minisat)

option(WITH_ASAN "Enabled AddressSanitizer to detect memory faults" OFF)
if(WITH_ASAN)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address,undefined" )
endif()
# create the main executable
## add additional .cpp files if needed
add_executable(ece650-prj ece650-prj.cpp )
# link MiniSAT libraries
target_link_libraries(ece650-prj minisat-lib-static)
# create the executable for tests
add_executable(ece650-optimized ece650-optimized.cpp )
# link MiniSAT libraries
target_link_libraries(ece650-optimized minisat-lib-static)
# create the executable for tests
add_executable(test test.cpp)
# link MiniSAT libraries
target_link_libraries(test minisat-lib-static)
