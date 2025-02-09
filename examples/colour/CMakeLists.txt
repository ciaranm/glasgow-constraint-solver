add_executable(colour colour.cc)
target_link_libraries(colour PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(colour LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME colour COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:colour>)
