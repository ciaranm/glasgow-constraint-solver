set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

if (GCS_COMPILER_HAS_GENERATOR)
else (GCS_COMPILER_HAS_GENERATOR)
    include_directories(${CMAKE_SOURCE_DIR}/generator/src/generator/include)
endif (GCS_COMPILER_HAS_GENERATOR)

add_subdirectory(break_table)
add_subdirectory(break_table_with_constants)
add_subdirectory(break_views)
add_subdirectory(up_proof)
add_subdirectory(consolidate_unary)
