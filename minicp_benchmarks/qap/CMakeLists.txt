add_executable(qap qap.cc)
target_link_libraries(qap PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(qap LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME qap-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:qap> 5)
