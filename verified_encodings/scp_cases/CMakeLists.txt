# Workflow-2 regression harness. Each curated .scp is solved and --proved by
# glasgow_scp_solver, re-derived by cake_pb_cp, checked by veripb (UNSAT *or*
# complete enumeration -- the (enumerate) element makes cake emit `preserved:`),
# and the two OPBs are compared by opbdiff --match-labels. Each test skips (77)
# when cake_pb_cp / veripb are absent. Most domains are bits-encoded on purpose,
# to keep the strict-opbdiff cases byte-clean; the binary_* cases below
# deliberately use a {0,1} model variable to exercise the binary b0 encoding
# (verified via the chain, not opbdiff -- see their `none` note).

set(_scp_chain_runner ${CMAKE_CURRENT_SOURCE_DIR}/../run_scp_chain.bash)

# add_scp_chain_test(<case> <opbdiff-mode>)  -- mode: strict | aux | none
function(add_scp_chain_test case mode)
    add_test(NAME scp_chain_${case}
        COMMAND ${_scp_chain_runner} $<TARGET_FILE:glasgow_scp_solver>
            ${CMAKE_CURRENT_SOURCE_DIR}/${case}.scp ${mode})
    set_tests_properties(scp_chain_${case} PROPERTIES SKIP_RETURN_CODE 77)
endfunction()

# strict: the solver's OPB matches cake's by label, exactly. Each family carries
# both a refutation (UNSAT) and a complete-enumeration (SAT) case where it can,
# since those are different proof shapes; the strict ops, multi-constraint and
# negative-domain cases widen the encoding paths exercised.
add_scp_chain_test(abs_unsat                strict)
add_scp_chain_test(abs_sat                  strict)
add_scp_chain_test(equals_unsat             strict)
add_scp_chain_test(equals_sat               strict)
add_scp_chain_test(less_equal_sat           strict)
add_scp_chain_test(less_equal_unsat         strict)
add_scp_chain_test(less_than_sat            strict)
add_scp_chain_test(less_than_unsat          strict)
add_scp_chain_test(greater_equal_unsat      strict)
add_scp_chain_test(greater_equal_sat        strict)
add_scp_chain_test(greater_than_unsat       strict)
add_scp_chain_test(greater_equal_neg_unsat  strict)  # two's-complement negative domains
add_scp_chain_test(lin_equals_unsat         strict)
add_scp_chain_test(lin_equals_sat           strict)
add_scp_chain_test(lin_equals_neg_coeff_sat strict)  # negative coefficient
add_scp_chain_test(lin_equals_3var_sat      strict)  # wider sum (3 terms)
add_scp_chain_test(lin_less_equal_unsat     strict)
add_scp_chain_test(lin_less_equal_sat       strict)
add_scp_chain_test(lin_greater_equal_unsat  strict)
add_scp_chain_test(multi_comparison_unsat   strict)  # two interacting comparisons
add_scp_chain_test(multi_mixed_unsat        strict)  # comparison + linear together

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

# none (chain-only): a {0,1} model variable is encoded as a single tautological
# line on i[v][b0], where cake emits two bound lines (lb + ub) on the same i[v][b0]
# -- so opbdiff sees cake's extra ub line ("only in B") and can't byte-match. The
# chain verifies regardless (the whole point of the relative-line work: VeriPB no
# longer pins the constraint count). Exercises the binary encoding both SAT
# (enumeration) and UNSAT.
add_scp_chain_test(binary_less_equal_sat  none)
add_scp_chain_test(binary_equals_unsat    none)

# none (chain-only): prim arithmetic (plus/minus) and logical (and/or) chain-
# verify, but the solver emits the equality halves / reified flags unlabelled
# where cake labels them @c[...], so opbdiff can't byte-match (same situation as
# all_different). minus is unsat-only: its SAT enumeration trips a RUP because
# cake encodes `minus a b z` as a = b + z, a strength mismatch on the rearranged
# bits (tracked with the count_sat enumeration gap).
add_scp_chain_test(plus_sat     none)
add_scp_chain_test(plus_unsat   none)
add_scp_chain_test(minus_unsat  none)
add_scp_chain_test(and_sat      none)
add_scp_chain_test(or_sat       none)
