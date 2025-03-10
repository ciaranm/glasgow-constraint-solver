set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
add_executable(fzn-glasgow fzn_glasgow.cc)
target_link_libraries(fzn-glasgow PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(fzn-glasgow LINK_PUBLIC ${Boost_LIBRARIES})
target_link_libraries(fzn-glasgow PRIVATE fmt::fmt)
target_link_libraries(fzn-glasgow PRIVATE nlohmann_json::nlohmann_json)

include_directories(${CMAKE_SOURCE_DIR}/generator/src/generator/include)

add_test(NAME minizinc-abs COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ abs true true)
set_tests_properties(minizinc-abs PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-among COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ amongtest true true)
set_tests_properties(minizinc-among PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arraybooland COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arraybooland true true)
set_tests_properties(minizinc-arraybooland PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayboolxor COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayboolxor true true)
set_tests_properties(minizinc-arrayboolxor PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayint COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayint true true)
set_tests_properties(minizinc-arrayint PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayintminmax COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayintminmax false true)
set_tests_properties(minizinc-arrayintminmax PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayvar COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayvar true true)
set_tests_properties(minizinc-arrayvar PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-aust COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ aust true true)
set_tests_properties(minizinc-aust PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-boolxor COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ boolxor true true)
set_tests_properties(minizinc-boolxor PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-cake COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cake false true)
set_tests_properties(minizinc-cake PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-count COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ counttest true true)
set_tests_properties(minizinc-count PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-crystalmaze COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ crystalmaze true true)
set_tests_properties(minizinc-crystalmaze PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjointdomain COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjointdomain true true)
set_tests_properties(minizinc-disjointdomain PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-div COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ div true true)
set_tests_properties(minizinc-div PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-equals COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ equals false true)
set_tests_properties(minizinc-equals PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-equalsreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ equalsreif true true)
set_tests_properties(minizinc-equalsreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-inverses COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inverses true true)
set_tests_properties(minizinc-inverses PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lessthans COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lessthans true true)
set_tests_properties(minizinc-lessthans PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-minmax COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ minmax false true)
set_tests_properties(minizinc-minmax PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-notequalsreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ notequalsreif true true)
set_tests_properties(minizinc-notequalsreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-regex COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ regex true true)
set_tests_properties(minizinc-regex PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-nurses COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ nurses true false)
set_tests_properties(minizinc-nurses PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-setinreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ setinreif true true)
set_tests_properties(minizinc-setinreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-sets COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ sets true true)
set_tests_properties(minizinc-sets PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-small COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ small true true)
set_tests_properties(minizinc-small PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-times COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ times true true)
set_tests_properties(minizinc-times PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tsp COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tsp false true)
set_tests_properties(minizinc-tsp PROPERTIES SKIP_RETURN_CODE 66)
