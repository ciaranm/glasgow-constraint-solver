add_executable(ortho_latin ortho_latin.cc)
target_link_libraries(ortho_latin PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(ortho_latin LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME ortho_latin-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:ortho_latin> 5)
