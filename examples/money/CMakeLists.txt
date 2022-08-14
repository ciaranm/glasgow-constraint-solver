add_executable(money money.cc)
target_link_libraries(money PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(money LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME money COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:money>)
