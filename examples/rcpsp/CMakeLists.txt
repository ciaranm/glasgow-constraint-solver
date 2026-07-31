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
