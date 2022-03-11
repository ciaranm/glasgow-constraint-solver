add_executable(ortho_latin ortho_latin.cc)
target_link_libraries(ortho_latin PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(ortho_latin LINK_PUBLIC ${Boost_LIBRARIES})
