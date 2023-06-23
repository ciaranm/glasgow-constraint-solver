add_executable(tutorial_proof tutorial_proof.cc)
target_link_libraries(tutorial_proof PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(tutorial_proof LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME tutorial_proof COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:tutorial_proof>)
