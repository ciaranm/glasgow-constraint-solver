add_executable(langford langford.cc)
target_link_libraries(langford PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(langford LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME langford COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:langford>)
