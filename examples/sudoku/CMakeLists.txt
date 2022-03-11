add_executable(sudoku sudoku.cc)
target_link_libraries(sudoku PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(sudoku LINK_PUBLIC ${Boost_LIBRARIES})
