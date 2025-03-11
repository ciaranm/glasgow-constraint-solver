add_executable(baby_tu_debug baby_tu_debug.cc)
target_link_libraries(baby_tu_debug PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(baby_tu_debug LINK_PUBLIC ${Boost_LIBRARIES})