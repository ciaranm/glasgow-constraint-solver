add_executable(fzn-glasgow fzn_glasgow.cc)
target_link_libraries(fzn-glasgow PRIVATE glasgow_constraint_solver cxxopts gcs_fmt nlohmann_json::nlohmann_json)

add_test(NAME minizinc-abs COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ abs true true)
set_tests_properties(minizinc-abs PROPERTIES SKIP_RETURN_CODE 66)

# MiniZinc rewrites `x = y` and `x != y` between two variables into a two-term
# int_lin_eq / int_lin_ne rather than emitting int_eq / int_ne, and the FlatZinc
# reader recovers the shape so the specialised propagators are reached at all.
# Both guards are load-bearing: --fzn-pattern pins that MiniZinc really does hand
# us the linear form (if a future version emits int_eq instead, the recovery is
# dead code and this says so), and the required output pattern pins that the
# recovery actually fired, counting the four sign patterns and *not* the
# variable-right-hand-side constraint, which is three terms and must fall through
# to LinearEquality. Without the second guard the test passes against a binary
# that does no recovery at all; without the enumeration diff a sign error in the
# normalisation passes too.
add_test(NAME minizinc-two-term-lin-eq COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern int_lin_eq $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ twotermlineq true true "-s" "propagatorCallsEqualsConstraints=4")
set_tests_properties(minizinc-two-term-lin-eq PROPERTIES SKIP_RETURN_CODE 66 ENVIRONMENT "GCS_PROPAGATOR_STATS=calls")

add_test(NAME minizinc-two-term-lin-ne COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern int_lin_ne $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ twotermlinne true true "-s" "propagatorCallsNotEqualsConstraints=4")
set_tests_properties(minizinc-two-term-lin-ne PROPERTIES SKIP_RETURN_CODE 66 ENVIRONMENT "GCS_PROPAGATOR_STATS=calls")

# The same for `x - y <= d`, which is the most common of the three shapes. The
# second lane is the one that matters: it pins that the recovered LessThanEqual
# still reaches the difference-logic presolver, which enumerates
# ReifiedCompareLessThanOrMaybeEqual donors as well as ReifiedLinearInequality
# ones -- six edges lifted either way, and through the comparison family after
# the rewrite, which is what differenceLogicComparisonEdgesLifted counts.
# These two are the only pair of minizinc lanes sharing a testname, and every
# scratch file run_minizinc_test.bash writes --- the .fzn, the captured output,
# the proof basename --- is named after it, so under a parallel ctest they
# clobber each other (the same hazard as issue #562, and it does fail: the
# difference-logic lane loses its output file to the plain one's run). The
# RESOURCE_LOCK serialises them.
add_test(NAME minizinc-two-term-lin-le COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern int_lin_le $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ twotermlinle true true "-s" "propagatorCallsLessEqualConstraints=8")
set_tests_properties(minizinc-two-term-lin-le PROPERTIES SKIP_RETURN_CODE 66 ENVIRONMENT "GCS_PROPAGATOR_STATS=calls"
    RESOURCE_LOCK twotermlinle)

add_test(NAME minizinc-two-term-lin-le-difference-logic COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern int_lin_le $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ twotermlinle true true "-s --difference-logic" "propagatorCallsLessEqualConstraints=8" "differenceLogicEdgesLifted=6" "differenceLogicComparisonEdgesLifted=6")
set_tests_properties(minizinc-two-term-lin-le-difference-logic PROPERTIES SKIP_RETURN_CODE 66 ENVIRONMENT "GCS_PROPAGATOR_STATS=calls"
    RESOURCE_LOCK twotermlinle)

add_test(NAME minizinc-alldifferentexcept COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ alldifferentexcept true true)
set_tests_properties(minizinc-alldifferentexcept PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-alldifferentexceptzero COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ alldifferentexceptzero true true)
set_tests_properties(minizinc-alldifferentexceptzero PROPERTIES SKIP_RETURN_CODE 66)

# The shapes a front end hands these globals (#1006): empty and single-element
# arrays, integer literals among the variables, arrays indexed from negative
# values, enum-typed arrays, and for the exception set, an empty set and one with
# a hole. Each model packs several shapes, so --fzn-count insists that every one
# of them reached the builtin rather than one being rewritten away behind the
# others. --reference-std adds the standard library's decompositions, since
# MiniZinc's default solver has its own all_different and alldifferent_except_0,
# and agreeing with a propagator and with a decomposition are different evidence.
# The except lane's count takes either builtin because MiniZinc 2.10's wrapper
# turns an empty exception set into a plain all_different before our
# redefinition is consulted, where 2.9 hands it over; the Linux lanes pin 2.9.7
# and the macOS ones take Homebrew's current release, so the count has to hold
# for both.
add_test(NAME minizinc-alldifferent-shapes COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 5 glasgow_alldifferent --reference-std $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ alldifferentshapes true true)
set_tests_properties(minizinc-alldifferent-shapes PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-alldifferentexcept-shapes COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 6 "glasgow_all_different_except_int|glasgow_alldifferent" --reference-std $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ alldifferentexceptshapes true true)
set_tests_properties(minizinc-alldifferentexcept-shapes PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-among COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ amongtest true true)
set_tests_properties(minizinc-among PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arraybooland COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arraybooland true true)
set_tests_properties(minizinc-arraybooland PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayboolxor COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayboolxor true true)
set_tests_properties(minizinc-arrayboolxor PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayint true true)
set_tests_properties(minizinc-arrayint PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayintminmax COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayintminmax false true)
set_tests_properties(minizinc-arrayintminmax PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-arrayvar COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ arrayvar true true)
set_tests_properties(minizinc-arrayvar PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-aust COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ aust true true)
set_tests_properties(minizinc-aust PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-binpacking COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ binpackingtest true true)
set_tests_properties(minizinc-binpacking PROPERTIES SKIP_RETURN_CODE 66)

# The bin offset the three bin_packing redefinitions pass, which fzn_glasgow
# applies as a view. --fzn-pattern is load-bearing on both: MiniZinc's
# bin_packing wrappers are free to rewrite into the library decomposition, which
# agrees with the reference solver and verifies its proof just as happily, and
# then the offset argument under test is never read. binpackingtest above is
# 1-based, where the offset is 1; these reach offsets of 5, 3 and 0, and
# binpackingloadtest is the only test of the variable-load form at all.
add_test(NAME minizinc-binpacking-offset COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_bin_packing_capa $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ binpackingoffsettest true true)
set_tests_properties(minizinc-binpacking-offset PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-binpacking-load COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_bin_packing_load $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ binpackingloadtest true true)
set_tests_properties(minizinc-binpacking-load PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-boolxor COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ boolxor true true)
set_tests_properties(minizinc-boolxor PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-cake COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cake false true)
set_tests_properties(minizinc-cake PROPERTIES SKIP_RETURN_CODE 66)

# --fzn-pattern is load-bearing on all three of these: without it they would pass
# against the stdlib decomposition, which agrees with the reference solver and
# verifies its proof just as happily, and nothing else the harness checks would
# notice that the builtin never ran.
add_test(NAME minizinc-circuit COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_circuit $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ circuittest true true)
set_tests_properties(minizinc-circuit PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-subcircuit COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_subcircuit $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ subcircuittest true true)
set_tests_properties(minizinc-subcircuit PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-subcircuit-evidence COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_subcircuit $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ subcircuitevidencetest true true)
set_tests_properties(minizinc-subcircuit-evidence PROPERTIES SKIP_RETURN_CODE 66)

# The reachability family. --fzn-pattern is the reachability guard: MiniZinc's
# connected / dconnected wrappers go through reachable / dreachable, so without
# it a test would still agree with the reference solver via the stdlib distance
# labelling even if the override never fired.
add_test(NAME minizinc-reachable COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_reachable $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ reachabletest true true)
set_tests_properties(minizinc-reachable PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-connected COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_reachable $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ connectedtest true true)
set_tests_properties(minizinc-connected PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-dreachable COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_dreachable $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ dreachabletest true true)
set_tests_properties(minizinc-dreachable PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-dconnected COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_dreachable $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ dconnectedtest true true)
set_tests_properties(minizinc-dconnected PROPERTIES SKIP_RETURN_CODE 66)

# tree / dtree / path / dpath ride one reachability encoding plus counting rules
# rather than the stdlib's distance labelling, and steiner and bounded_dpath ride
# those in turn through the stdlib's own wrappers. Each guard names the builtin
# that must appear in the flattened model, because without one the test would
# pass vacuously against the decomposition.
add_test(NAME minizinc-subgraph COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_subgraph $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ subgraphtest true true)
set_tests_properties(minizinc-subgraph PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-dag COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_dag $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ dagtest true true)
set_tests_properties(minizinc-dag PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tree COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_tree $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ treetest true true)
set_tests_properties(minizinc-tree PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-dtree COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_dtree $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ dtreetest true true)
set_tests_properties(minizinc-dtree PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-path COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_path $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ pathtest true true)
set_tests_properties(minizinc-path PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-dpath COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_dpath $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ dpathtest true true)
set_tests_properties(minizinc-dpath PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-steiner COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_tree $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ steinertest false true)
set_tests_properties(minizinc-steiner PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-bounded-dpath COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_dpath $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ boundeddpathtest false true)
set_tests_properties(minizinc-bounded-dpath PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-count COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ counttest true true)
set_tests_properties(minizinc-count PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-cumulative COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cumulativetest false true)
set_tests_properties(minizinc-cumulative PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-cumulative-mode COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cumulativemodetest true true)
set_tests_properties(minizinc-cumulative-mode PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-cumulative-var COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cumulativevartest true true)
set_tests_properties(minizinc-cumulative-var PROPERTIES SKIP_RETURN_CODE 66)

# Optional tasks. --fzn-pattern is the reachability guard: MiniZinc's cumulative
# wrapper is free to rewrite the constraint into a decomposition, and if it did,
# these tests would agree with the default solver and verify their proofs
# without glasgow_cumulative_opt ever running.
add_test(NAME minizinc-cumulative-opt COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_cumulative_opt --reference-solver chuffed $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cumulativeopttest true true)
set_tests_properties(minizinc-cumulative-opt PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-cumulative-opt-obj COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_cumulative_opt --reference-solver chuffed $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cumulativeoptobjtest false true)
set_tests_properties(minizinc-cumulative-opt-obj PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjunctive-opt COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_disjunctive_opt --reference-solver chuffed $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjunctiveopttest true true)
set_tests_properties(minizinc-disjunctive-opt PROPERTIES SKIP_RETURN_CODE 66)

# The strict optional form, which had no redefinition at all before #735: no
# route through cumulative can express "a present zero-duration task may not sit
# inside another", so this one used to keep the library decomposition and go
# uncertified.
add_test(NAME minizinc-disjunctive-strict-opt COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_disjunctive_strict_opt --reference-solver chuffed $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjunctivestrictopttest true true)
set_tests_properties(minizinc-disjunctive-strict-opt PROPERTIES SKIP_RETURN_CODE 66)

# The difference-logic presolver is invisible to solution equivalence and to
# proof verification alike, so this one also asserts on its counters: four
# lifted edges over four nodes, and the two constraints that are not
# difference-shaped classified rather than quietly ignored. The zero says
# all four arrived as `int_lin_le`, which is the whole reason this needs no
# predicate of its own; a flattener that started emitting `int_le` would
# still lift four edges, but they would be counted here instead.
#
# These names are also the contract between ComponentStats::entries() and the
# generic %%%mzn-stat loop in fzn_glasgow.cc: each is component_name() and an
# entry name camel-cased together, so a rename on either side fails here rather
# than in whatever is parsing the output. differenceLogicPropagatorInstalled is
# one of the two fields that were filled in and reported to nobody until the
# loop replaced the hand-written list, and is here so that stays fixed.
add_test(NAME minizinc-differencelogic COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ differencelogic true true
    "-s --difference-logic"
    "^%%%mzn-stat: differenceLogicEdgesLifted=4$"
    # Four via the comparison family, because the FlatZinc reader recovers a
    # two-term int_lin_le as LessThanEqual: the presolver enumerates both donor
    # families, so the same four edges lift, and this counter is what says which
    # way in. It was 0 before that recovery existed.
    "^%%%mzn-stat: differenceLogicComparisonEdgesLifted=4$"
    "^%%%mzn-stat: differenceLogicNodes=4$"
    "^%%%mzn-stat: differenceLogicSkippedNotTwoTerms=1$"
    "^%%%mzn-stat: differenceLogicSkippedCoefficients=1$"
    "^%%%mzn-stat: differenceLogicPropagatorInstalled=1$"
    "^%%%mzn-stat: differenceLogicSimplifyRan=1$")
set_tests_properties(minizinc-differencelogic PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjunctive COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjunctivetest true true)
set_tests_properties(minizinc-disjunctive PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjunctivestrict COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjunctivestricttest true true)
set_tests_properties(minizinc-disjunctivestrict PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjunctive-var COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjunctivevartest true true)
set_tests_properties(minizinc-disjunctive-var PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjunctive-var-nonstrict COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjunctivevarnonstricttest true true)
set_tests_properties(minizinc-disjunctive-var-nonstrict PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-diffn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ diffntest true true)
set_tests_properties(minizinc-diffn PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-diffn-rotate COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ diffnrotatetest true true)
set_tests_properties(minizinc-diffn-rotate PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-diffn-nonstrict COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ diffnnonstricttest true true)
set_tests_properties(minizinc-diffn-nonstrict PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-countops COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ countops true true)
set_tests_properties(minizinc-countops PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-crystalmaze COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ crystalmaze true true)
set_tests_properties(minizinc-crystalmaze PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-decreasing COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ decreasing true true)
set_tests_properties(minizinc-decreasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-disjointdomain COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ disjointdomain true true)
set_tests_properties(minizinc-disjointdomain PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-div COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ div true true)
set_tests_properties(minizinc-div PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-equals COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ equals false true)
set_tests_properties(minizinc-equals PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-equalsreif COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ equalsreif true true)
set_tests_properties(minizinc-equalsreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-globalcardinality COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ globalcardinality true true)
set_tests_properties(minizinc-globalcardinality PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-globalcardinalityclosed COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ globalcardinalityclosed true true)
set_tests_properties(minizinc-globalcardinalityclosed PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-globalcardinalitylowup COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ globalcardinalitylowup true true)
set_tests_properties(minizinc-globalcardinalitylowup PROPERTIES SKIP_RETURN_CODE 66)

# A cover that repeats a value, which MiniZinc permits and GlobalCardinality does
# not: the front end folds the repeat out and posts the count equality it stood
# for (#922). The fzn pattern is what stops these passing vacuously -- if the
# repeat were folded by MiniZinc's own wrapper instead, the solutions would still
# agree and the builtin under test would never have run.
add_test(NAME minizinc-globalcardinalityrepeated COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_global_cardinality $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ globalcardinalityrepeated true true)
set_tests_properties(minizinc-globalcardinalityrepeated PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-globalcardinalityrepeatedclosed COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_global_cardinality_closed $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ globalcardinalityrepeatedclosed true true)
set_tests_properties(minizinc-globalcardinalityrepeatedclosed PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-increasing COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ increasing true true)
set_tests_properties(minizinc-increasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-inverses COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inverses true true)
set_tests_properties(minizinc-inverses PROPERTIES SKIP_RETURN_CODE 66)

# The index sets the three index-valued alldifferent-family globals were given
# in the model (#987): the flattened arrays are 1-based whatever the model's
# were, so the redefinitions pass them explicitly. --fzn-pattern is load-bearing,
# as for circuit: the stdlib decomposition agrees with the reference solver and
# verifies its proof whatever the builtin would have done.
add_test(NAME minizinc-inverses-offset COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_inverse $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inversesoffset true true)
set_tests_properties(minizinc-inverses-offset PROPERTIES SKIP_RETURN_CODE 66)

# More of the shapes a front end can misread for the index-valued globals
# (#1006), several to a model, so --fzn-count guards each. The -negative lanes
# are the shapes MiniZinc's default solver gets wrong itself: its own inverse,
# which symmetric_all_different reaches through the stdlib, reports
# `Int::channel: Number out of limits` on a negative index set and calls an
# empty pair of arrays unsatisfiable. So those compare against the standard
# library's decompositions alone, and the others against both.
add_test(NAME minizinc-inverses-shapes COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 4 glasgow_inverse --reference-std $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inversesshapes true true)
set_tests_properties(minizinc-inverses-shapes PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-inverses-negative COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 2 glasgow_inverse --reference-std --skip-default-reference $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inversesnegative true true)
set_tests_properties(minizinc-inverses-negative PROPERTIES SKIP_RETURN_CODE 66)

# Arrays of different lengths, which the redefinition turns into `false` before
# any builtin is posted. The default solver errors on the mismatch instead of
# reporting it, and the flattener never runs a solver on a model it has already
# found inconsistent, so there is no proof to check.
add_test(NAME minizinc-inverses-unequal COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --unsatisfiable --reference-std --skip-default-reference $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ inversesunequal true false)
set_tests_properties(minizinc-inverses-unequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-knapsack COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ knapsacktest false true)
set_tests_properties(minizinc-knapsack PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lessthans COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lessthans true true)
set_tests_properties(minizinc-lessthans PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexbool COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexbool true true)
set_tests_properties(minizinc-lexbool PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexgequnequal COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexgequnequal true true)
set_tests_properties(minizinc-lexgequnequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexgtunequal COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexgtunequal true true)
set_tests_properties(minizinc-lexgtunequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexlequnequal COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexlequnequal true true)
set_tests_properties(minizinc-lexlequnequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexless COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexless true true)
set_tests_properties(minizinc-lexless PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexlesseq COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexlesseq true true)
set_tests_properties(minizinc-lexlesseq PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexltunequal COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexltunequal true true)
set_tests_properties(minizinc-lexltunequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-lexreif COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ lexreif true true)
set_tests_properties(minizinc-lexreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-mdd COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ mddtest true true)
set_tests_properties(minizinc-mdd PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-allequal COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ allequaltest true true)
set_tests_properties(minizinc-allequal PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-member COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ membertest true true)
set_tests_properties(minizinc-member PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-minmax COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ minmax false true)
set_tests_properties(minizinc-minmax PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-notequalsreif COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ notequalsreif true true)
set_tests_properties(minizinc-notequalsreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-nvalue COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ nvaluetest true true)
set_tests_properties(minizinc-nvalue PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ regex true true)
set_tests_properties(minizinc-regex PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-nurses COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ nurses true false)
set_tests_properties(minizinc-nurses PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-seqprecedechain COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ seqprecedechain true true)
set_tests_properties(minizinc-seqprecedechain PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-seqwdeg COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ seqwdeg true true)
set_tests_properties(minizinc-seqwdeg PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-setinreif COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ setinreif true true)
set_tests_properties(minizinc-setinreif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-sets COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ sets true true)
set_tests_properties(minizinc-sets PROPERTIES SKIP_RETURN_CODE 66)

# Empty-set set_in / set_in_reif: MiniZinc folds `x in {}` to false before it
# reaches the solver, so these feed hand-written JSON FlatZinc to fzn-glasgow
# directly to exercise the empty-set frontend guards.
# Pins the glasgow_cumulative_opt signature against the solver directly, so a
# MiniZinc version that re-routes around the builtin cannot take this coverage
# with it. The expected solutions are the hand-countable set: 9 with both tasks
# absent, 9 with each alone, and the 2 non-overlapping placements with both.
add_test(NAME minizinc-cumulativeopt-fzn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_fzn_json_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ cumulative_opt)

add_test(NAME minizinc-emptysetin COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_fzn_json_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ empty_set_in)
add_test(NAME minizinc-emptysetinreif COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_fzn_json_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ empty_set_in_reif)

# A var bool output array whose every element the flattener has fixed (#785).
# This has to be hand-written JSON: MiniZinc drops such an array from `output`
# unless something else keeps it alive, so a .mzn model cannot reach it. `ns` is
# the all-par array that used to print as 1 / 0; `es` keeps one live variable, so
# it prints correctly either way and shows the two disagreeing in one solution;
# `ds` is all-par ints, and is here so the fix cannot start calling those bools.
add_test(NAME minizinc-parboolarrayoutput COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_fzn_json_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ par_bool_array_output)

add_test(NAME minizinc-small COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ small true true)
set_tests_properties(minizinc-small PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-sort COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ sorttest true true)
set_tests_properties(minizinc-sort PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-argsort COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ argsorttest true true)
set_tests_properties(minizinc-argsort PROPERTIES SKIP_RETURN_CODE 66)

# As minizinc-inverses-offset.
add_test(NAME minizinc-argsort-offset COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_arg_sort_int $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ argsortoffset true true)
set_tests_properties(minizinc-argsort-offset PROPERTIES SKIP_RETURN_CODE 66)

# As minizinc-inverses-shapes. There is no --reference-std: MiniZinc's default
# solver has no arg_sort of its own, so it already runs the stdlib decomposition.
add_test(NAME minizinc-argsort-shapes COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 5 glasgow_arg_sort_int $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ argsortshapes true true)
set_tests_properties(minizinc-argsort-shapes PROPERTIES SKIP_RETURN_CODE 66)

# A reified and a half-reified arg_sort, which failed to flatten at all until
# the redefinition included the stdlib's reified decomposition: nothing else
# reaches that include, since every other lane posts arg_sort at the root.
add_test(NAME minizinc-argsort-reif COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ argsortreif true true)
set_tests_properties(minizinc-argsort-reif PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-splitrandom COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ splitrandom true true)
set_tests_properties(minizinc-splitrandom PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-strictlydecreasing COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ strictlydecreasing true true)
set_tests_properties(minizinc-strictlydecreasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-strictlyincreasing COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ strictlyincreasing true true)
set_tests_properties(minizinc-strictlyincreasing PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-symmetricalldifferent COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ symmetricalldifferent true true)
set_tests_properties(minizinc-symmetricalldifferent PROPERTIES SKIP_RETURN_CODE 66)

# As minizinc-inverses-offset.
add_test(NAME minizinc-symmetricalldifferent-offset COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-pattern glasgow_symmetric_all_different $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ symmetricalldifferentoffset true true)
set_tests_properties(minizinc-symmetricalldifferent-offset PROPERTIES SKIP_RETURN_CODE 66)

# As minizinc-inverses-shapes and minizinc-inverses-negative.
add_test(NAME minizinc-symmetricalldifferent-shapes COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 4 glasgow_symmetric_all_different --reference-std $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ symmetricalldifferentshapes true true)
set_tests_properties(minizinc-symmetricalldifferent-shapes PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-symmetricalldifferent-negative COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash --fzn-count 2 glasgow_symmetric_all_different --reference-std --skip-default-reference $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ symmetricalldifferentnegative true true)
set_tests_properties(minizinc-symmetricalldifferent-negative PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tablebool COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tablebool true true)
set_tests_properties(minizinc-tablebool PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tableint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tableint true true)
set_tests_properties(minizinc-tableint PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-times COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ times true true)
set_tests_properties(minizinc-times PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-tsp COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ tsp false true)
set_tests_properties(minizinc-tsp PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-valueprecede COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ valueprecede true true)
set_tests_properties(minizinc-valueprecede PROPERTIES SKIP_RETURN_CODE 66)

add_test(NAME minizinc-valueprecedechain COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/minizinc/run_minizinc_test.bash $<TARGET_FILE:fzn-glasgow> ${CMAKE_SOURCE_DIR}/minizinc/ valueprecedechain true true)
set_tests_properties(minizinc-valueprecedechain PROPERTIES SKIP_RETURN_CODE 66)
