add_executable(fzn-glasgow fzn_glasgow.cc)
target_link_libraries(fzn-glasgow PRIVATE glasgow_constraint_solver cxxopts gcs_fmt nlohmann_json::nlohmann_json)

add_test(NAME minizinc-abs COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ abs true true)
set_tests_properties(minizinc-abs PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-alldifferentexcept COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ alldifferentexcept true true)
set_tests_properties(minizinc-alldifferentexcept PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-alldifferentexceptzero COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ alldifferentexceptzero true true)
set_tests_properties(minizinc-alldifferentexceptzero PROPERTIES SKIP_RETURN_CODE 66)

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

add_test(NAME minizinc-countops COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ countops true true)
set_tests_properties(minizinc-countops PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-crystalmaze COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ crystalmaze true true)
set_tests_properties(minizinc-crystalmaze PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-decreasing COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ decreasing true true)
set_tests_properties(minizinc-decreasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjointdomain COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjointdomain true true)
set_tests_properties(minizinc-disjointdomain PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-div COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ div true true)
set_tests_properties(minizinc-div PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-equals COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ equals false true)
set_tests_properties(minizinc-equals PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-equalsreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ equalsreif true true)
set_tests_properties(minizinc-equalsreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-increasing COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ increasing true true)
set_tests_properties(minizinc-increasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-inverses COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inverses true true)
set_tests_properties(minizinc-inverses PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-knapsack COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ knapsacktest false true)
set_tests_properties(minizinc-knapsack PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lessthans COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lessthans true true)
set_tests_properties(minizinc-lessthans PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexbool COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexbool true true)
set_tests_properties(minizinc-lexbool PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexgequnequal COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexgequnequal true true)
set_tests_properties(minizinc-lexgequnequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexgtunequal COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexgtunequal true true)
set_tests_properties(minizinc-lexgtunequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexlequnequal COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexlequnequal true true)
set_tests_properties(minizinc-lexlequnequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexless COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexless true true)
set_tests_properties(minizinc-lexless PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexlesseq COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexlesseq true true)
set_tests_properties(minizinc-lexlesseq PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexltunequal COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexltunequal true true)
set_tests_properties(minizinc-lexltunequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexreif true true)
set_tests_properties(minizinc-lexreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-allequal COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ allequaltest true true)
set_tests_properties(minizinc-allequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-member COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ membertest true true)
set_tests_properties(minizinc-member PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-minmax COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ minmax false true)
set_tests_properties(minizinc-minmax PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-notequalsreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ notequalsreif true true)
set_tests_properties(minizinc-notequalsreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-nvalue COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ nvaluetest true true)
set_tests_properties(minizinc-nvalue PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-regex COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ regex true true)
set_tests_properties(minizinc-regex PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-nurses COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ nurses true false)
set_tests_properties(minizinc-nurses PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-seqprecedechain COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ seqprecedechain true true)
set_tests_properties(minizinc-seqprecedechain PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-setinreif COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ setinreif true true)
set_tests_properties(minizinc-setinreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-sets COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ sets true true)
set_tests_properties(minizinc-sets PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-small COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ small true true)
set_tests_properties(minizinc-small PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-strictlydecreasing COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ strictlydecreasing true true)
set_tests_properties(minizinc-strictlydecreasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-strictlyincreasing COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ strictlyincreasing true true)
set_tests_properties(minizinc-strictlyincreasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-symmetricalldifferent COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ symmetricalldifferent true true)
set_tests_properties(minizinc-symmetricalldifferent PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tablebool COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tablebool true true)
set_tests_properties(minizinc-tablebool PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tableint COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tableint true true)
set_tests_properties(minizinc-tableint PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-times COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ times true true)
set_tests_properties(minizinc-times PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tsp COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tsp false true)
set_tests_properties(minizinc-tsp PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-valueprecede COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ valueprecede true true)
set_tests_properties(minizinc-valueprecede PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-valueprecedechain COMMAND ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ valueprecedechain true true)
set_tests_properties(minizinc-valueprecedechain PROPERTIES SKIP_RETURN_CODE 66)
