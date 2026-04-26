set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})

if (GCS_COMPILER_HAS_GENERATOR)
else (GCS_COMPILER_HAS_GENERATOR)
    include_directories(${CMAKE_SOURCE_DIR}/generator/src/generator/include)
endif (GCS_COMPILER_HAS_GENERATOR)

add_subdirectory(magic_series)
add_subdirectory(magic_square)
add_subdirectory(n_queens)
add_subdirectory(qap)
add_subdirectory(tsp)
