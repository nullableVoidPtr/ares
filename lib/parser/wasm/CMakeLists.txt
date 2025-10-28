cmake_minimum_required(VERSION 3.20)
project(HermesBytecode LANGUAGES CXX)

find_package(Git QUIET)
if(GIT_FOUND AND EXISTS "${PROJECT_SOURCE_DIR}/.git")
# Update submodules as needed
    option(GIT_SUBMODULE "Check submodules during build" ON)
    if(GIT_SUBMODULE)
        message(STATUS "Submodule update")
        execute_process(COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive
                        WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                        RESULT_VARIABLE GIT_SUBMOD_RESULT)
        if(NOT GIT_SUBMOD_RESULT EQUAL "0")
            message(FATAL_ERROR "git submodule update --init --recursive failed with ${GIT_SUBMOD_RESULT}, please checkout submodules")
        endif()
    endif()
endif()

if(NOT EXISTS "${PROJECT_SOURCE_DIR}/kaitai_struct_cpp_stl_runtime/CMakeLists.txt")
    message(FATAL_ERROR "The submodules were not downloaded! GIT_SUBMODULE was turned off or failed. Please update submodules and try again.")
endif()

if(NOT "${CMAKE_CXX_COMPILER}" MATCHES "em\\+\\+")
	message(FATAL_ERROR "This project must be built with em++ (Emscripten). Example:\n  emcmake cmake .. && emmake make")
endif()


set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

option(BUILD_TESTS "" OFF)
add_subdirectory(kaitai_struct_cpp_stl_runtime)

find_program(KAITAI_STRUCT_COMPILER kaitai-struct-compiler 
    PATHS /usr/local/bin /usr/bin
)

if(NOT KAITAI_STRUCT_COMPILER)
    message(FATAL_ERROR "ksc not found.")
endif()


set(KAITAI_SOURCES
	../ksy/hermes_bytecode.ksy
	../ksy/vlq_base128_le.ksy
)

set(KAITAI_OUTPUT_DIR "${CMAKE_CURRENT_BINARY_DIR}/ksy")

foreach(src ${KAITAI_SOURCES})
	get_filename_component(name ${src} NAME_WE)
	list(APPEND KAITAI_CPP "${KAITAI_OUTPUT_DIR}/${name}.cpp")
	list(APPEND KAITAI_H "${KAITAI_OUTPUT_DIR}/${name}.h")
endforeach()

set(KAITAI_CPP ${KAITAI_CPP})
set(KAITAI_H ${KAITAI_H})

add_custom_command(
	OUTPUT ${KAITAI_CPP} ${KAITAI_H}
	COMMAND ${KAITAI_STRUCT_COMPILER}
		--target cpp_stl
		--outdir ${KAITAI_OUTPUT_DIR}
		${CMAKE_CURRENT_SOURCE_DIR}/../ksy/hermes_bytecode.ksy
	DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/../ksy/hermes_bytecode.ksy
	COMMENT "Generating C++ parser from hermes_bytecode.ksy"
	VERBATIM
)

add_custom_target(generate_kaitai_parser
	DEPENDS ${KAITAI_CPP}
)

# Output target
add_executable(hermes_bytecode main.cpp)
add_dependencies(hermes_bytecode generate_kaitai_parser)
target_sources(hermes_bytecode PRIVATE ${KAITAI_CPP})
target_include_directories(hermes_bytecode PRIVATE ${KAITAI_OUTPUT_DIR})
target_link_libraries(hermes_bytecode kaitai_struct_cpp_stl_runtime)

# Set output file name and extension
set_target_properties(hermes_bytecode PROPERTIES
  OUTPUT_NAME "hermes_bytecode"
  SUFFIX ".mjs"
)

target_link_options(hermes_bytecode PRIVATE
  "SHELL:-s ASSERTIONS=1 -s ALLOW_MEMORY_GROWTH=1"
  "SHELL:-s MODULARIZE=1 -s EXPORT_ES6=1 -s SINGLE_FILE=1"
  "SHELL:-s EXPORT_NAME=HermesBytecodeModule"
  "SHELL:--emit-tsd hermes_bytecode.d.ts"
  "SHELL:--bind"
)