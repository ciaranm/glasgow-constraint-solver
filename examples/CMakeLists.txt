set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
include_directories(${CMAKE_SOURCE_DIR}/generator/src/generator/include)
add_subdirectory(auto_table)
add_subdirectory(cake)
add_subdirectory(colour)
add_subdirectory(circuit_small)
add_subdirectory(circuit_random)
add_subdirectory(crystal_maze)
add_subdirectory(knapsack)
add_subdirectory(langford)
add_subdirectory(money)
add_subdirectory(n_fractions)
add_subdirectory(odd_even_sum)
add_subdirectory(ortho_latin)
add_subdirectory(random_regular)
add_subdirectory(regex)
add_subdirectory(rostering)
add_subdirectory(skeleton_puzzle)
add_subdirectory(skyscrapers)
add_subdirectory(smart_table_am1)
add_subdirectory(smart_table_lex)
add_subdirectory(smart_table_random)
add_subdirectory(smart_table_small)
add_subdirectory(sudoku)
add_subdirectory(tour)
add_subdirectory(tutorial_proof)
add_subdirectory(talent)