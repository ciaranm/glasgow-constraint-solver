set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
add_executable(fzn-glasgow fzn_glasgow.cc)
target_link_libraries(fzn-glasgow PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(fzn-glasgow LINK_PUBLIC ${Boost_LIBRARIES})
target_link_libraries(fzn-glasgow PRIVATE fmt::fmt)
target_link_libraries(fzn-glasgow PRIVATE nlohmann_json::nlohmann_json)
