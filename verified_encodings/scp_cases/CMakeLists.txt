# Workflow-2 regression harness. Each curated .scp is solved and --proved by
# glasgow_scp_solver, re-derived by cake_pb_cp, checked by veripb (UNSAT *or*
# complete enumeration -- the (enumerate) element makes cake emit `preserved:`),
# and the two OPBs are compared by opbdiff --match-labels. Each test skips (77)
# when cake_pb_cp / veripb are absent. Domains are bits-encoded on purpose, to
# avoid the direct-only-vs-bits divergence; reified forms are deferred for the
# same reason (their [0,1] condition variable is direct-encoded).

set(_scp_chain_runner ${CMAKE_CURRENT_SOURCE_DIR}/../run_scp_chain.bash)

# add_scp_chain_test(<case> <opbdiff-mode>)  -- mode: strict | aux | none
function(add_scp_chain_test case mode)
    add_test(NAME scp_chain_${case}
        COMMAND ${_scp_chain_runner} $<TARGET_FILE:glasgow_scp_solver>
            ${CMAKE_CURRENT_SOURCE_DIR}/${case}.scp ${mode})
    set_tests_properties(scp_chain_${case} PROPERTIES SKIP_RETURN_CODE 77)
endfunction()

# strict: the solver's OPB matches cake's by label, exactly.
add_scp_chain_test(abs_unsat            strict)
add_scp_chain_test(less_equal_sat       strict)
add_scp_chain_test(less_equal_unsat     strict)
add_scp_chain_test(greater_equal_unsat  strict)
add_scp_chain_test(lin_less_equal_unsat strict)

# TODO: upgrade equals_unsat / lin_equals_unsat to `strict` once the
# equals/linear @c[id][le]/[ge] labelling (PR #275) is merged -- the chain
# already verifies; only the opbdiff label check awaits those labels.
add_scp_chain_test(equals_unsat         none)
add_scp_chain_test(lin_equals_unsat     none)

# aux: matches modulo a constraint-local selector flag's *name* -- cake names
# not_equals' flag b[name][ne], the solver f[N][gt], but with the same polarity,
# so the @c lines still match once names are ignored.
add_scp_chain_test(not_equals_sat       aux)
add_scp_chain_test(lin_not_equals_sat   aux)

# none (chain-only): all_different's per-pair selector has the *opposite* polarity
# to cake's (the deferred conform-the-solver item), and multiple identical-looking
# selectors defeat aux-name matching anyway -- so the chain (which verifies
# regardless: the flag is existential) is the oracle here, not opbdiff.
add_scp_chain_test(all_different_unsat  none)
add_scp_chain_test(all_different_sat    none)
