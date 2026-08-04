add_executable(rcpsp rcpsp.cc)
target_link_libraries(rcpsp PRIVATE glasgow_constraint_solver)
target_link_libraries(rcpsp PRIVATE cxxopts)

# Three registrations, covering the three proof conclusions and branchings this
# example can reach. They need distinct basenames so that a parallel ctest does
# not race them over one set of proof files (#562).
add_test(NAME rcpsp COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:rcpsp>)

# The decision variant, with a deadline below the optimal makespan, so this
# entry covers the UNSATISFIABLE conclusion as well as the BOUNDS one above.
add_test(NAME rcpsp_deadline COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_deadline
    $<TARGET_FILE:rcpsp> --size 14 --seed 0 --deadline 16)

# Bisecting a start time's domain rather than enumerating it, which makes the
# search decisions inequalities rather than equalities, and so gives the
# scheduling propagators a different proof shape to justify.
add_test(NAME rcpsp_split COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_split
    $<TARGET_FILE:rcpsp> --value-order split)

# RCPSP/max: maximum time lags, so the network of difference constraints has
# cycles rather than being a DAG. Seed 3 at this size actually gets some; a
# smaller one can draw none at all, which would make this a duplicate of the
# first entry without saying so.
add_test(NAME rcpsp_max_lags COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_max_lags
    $<TARGET_FILE:rcpsp> --size 12 --seed 3 --max-lag-density 0.3)

# A maximum lag tightened one unit past its longest path, so the instance is
# unsatisfiable through a negative cycle that no single constraint is violated
# by. Root propagation refutes it before search ever starts, so the conclusion
# is BOUNDS INF <= obj <= INF rather than rcpsp_deadline's UNSATISFIABLE: the
# same fact, reached as an optimisation with no feasible solution rather than as
# a decision. Discriminating: the same instance without --infeasible is optimal
# at makespan 12 in 82 recursions, and with a slack-2 lag instead is optimal at
# 14, so this entry fails if the tightening stops biting.
add_test(NAME rcpsp_infeasible COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_infeasible
    $<TARGET_FILE:rcpsp> --size 8 --seed 1 --infeasible)

# The ProGen/max .sch reader, on an instance whose arcs are start-to-start and
# include a maximum lag, and which has a dummy source and sink of zero duration.
add_test(NAME rcpsp_sch COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_sch
    $<TARGET_FILE:rcpsp> --file ${CMAKE_CURRENT_SOURCE_DIR}/sample.sch)

# The plain-RCPSP .dzn reader, which is a different format entirely: a demand
# matrix and finish-to-start successor sets rather than a token stream of
# start-to-start arcs.
add_test(NAME rcpsp_dzn COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_dzn
    $<TARGET_FILE:rcpsp> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn)

# The same instance with the InferredDisjunctive presolver, whose derived
# capacity-one Cumulative is proved rather than asserted --- so this is the
# end-to-end proof check for that certificate on a model read from a file, as
# opposed to the presolver's own fixtures. sample.dzn is built so that each
# conflicting pair is witnessed by a different resource, which is the case no
# single posted Cumulative can reach; the presolver reports a capacity bound of
# 6, and the optimum is 6.
add_test(NAME rcpsp_dzn_inferred COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_dzn_inferred
    $<TARGET_FILE:rcpsp> --dzn ${CMAKE_CURRENT_SOURCE_DIR}/sample.dzn --infer-disjunctive)

# Enumeration rather than optimisation, so this one reaches the COMPLETE
# ENUMERATION conclusion, which none of the others do.
add_test(NAME rcpsp_all COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_all
    $<TARGET_FILE:rcpsp> --size 5 --seed 2 --resources 1 --all)

# A capacity-one resource posted as Disjunctive rather than Cumulative. The two
# must search identically --- both are time-table at capacity one --- so this
# covers the Disjunctive proof path over a resource rather than over the machine.
add_test(NAME rcpsp_unary COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_unary
    $<TARGET_FILE:rcpsp> --size 10 --seed 4 --resources 1 --capacity 1 --max-demand 1 --unary disjunctive)

# The temporal network through the global propagator, and through the presolver
# that lifts it back out of the decomposition, on the same maximum-lag instance
# rcpsp_max_lags posts decomposed. All three reach makespan 14 in 61 recursions
# --- --branch is a static order, so the search is an invariant across variants
# --- and differ only in propagations, which is the point of the comparison.
add_test(NAME rcpsp_global COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_global
    $<TARGET_FILE:rcpsp> --size 12 --seed 3 --max-lag-density 0.3 --variant global)
add_test(NAME rcpsp_presolved COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_presolved
    $<TARGET_FILE:rcpsp> --size 12 --seed 3 --max-lag-density 0.3 --variant presolved)

# The negative cycle through the global propagator: refuted at the root, with a
# refutation that sums the cycle's edge rows rather than crawling bounds.
add_test(NAME rcpsp_global_infeasible COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_global_infeasible
    $<TARGET_FILE:rcpsp> --size 8 --seed 1 --infeasible --variant global)

# --machine=difference, which is what puts *conditional* edges into the network,
# in each of the three variants. All three must reach the same optimum as
# --machine=disjunctive and --machine=pairwise --- they say the same thing --- but
# unlike the unconditional network they do not search alike: the reified linears
# infer their condition and DifferenceConstraints does not (IncImp is deliberately
# absent), so global explores more nodes with fewer propagations. That divergence
# is the point of having all three.
add_test(NAME rcpsp_machine_difference COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_machine_difference
    $<TARGET_FILE:rcpsp> --size 10 --seed 5 --machine-fraction 0.7 --machine difference)
add_test(NAME rcpsp_machine_difference_global COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_machine_difference_global
    $<TARGET_FILE:rcpsp> --size 10 --seed 5 --machine-fraction 0.7 --machine difference --variant global)
add_test(NAME rcpsp_machine_difference_presolved COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_machine_difference_presolved
    $<TARGET_FILE:rcpsp> --size 10 --seed 5 --machine-fraction 0.7 --machine difference --variant presolved)

# The same conditional-edge instance with the root simplification stage off, so
# the fallback path keeps being proof-checked. With the stage on, 14 redundant
# edges go and 9 conditions are fixed before search; with it off the solver has
# to find all of that itself, and those are two different proofs of the same
# optimum.
add_test(NAME rcpsp_machine_difference_nosimplify COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_machine_difference_nosimplify
    $<TARGET_FILE:rcpsp> --size 10 --seed 5 --machine-fraction 0.7 --machine difference --variant global --simplify off)
add_test(NAME rcpsp_machine_difference_presolved_nosimplify COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename rcpsp_machine_difference_presolved_nosimplify
    $<TARGET_FILE:rcpsp> --size 10 --seed 5 --machine-fraction 0.7 --machine difference --variant presolved --simplify off)
