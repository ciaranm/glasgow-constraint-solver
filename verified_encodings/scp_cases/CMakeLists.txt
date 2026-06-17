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

# strict: not_equals' single selector is now named b[id][ne] with cake's
# polarity (selector TRUE = gt half, FALSE = lt half), via the
# create_proof_flag(ConstraintID, annotation) overload -- the first consumer of
# the scalar `b[...]` aux-naming pattern (#354), the b[...] analogue of
# all_different for `x[...]`. The proof never references the selector by name
# (the propagator prunes by RUP / domain-disjointness), so this is a pure
# OPB-definition rename, and both the integer and linear forms (cake's shared
# `nev` selector) now byte-match cake. SAT enumerates both selector halves; the
# UNSAT cases (operands forced equal) exercise the refutation proof shape.
add_scp_chain_test(not_equals_sat       strict)
add_scp_chain_test(not_equals_unsat     strict)
add_scp_chain_test(lin_not_equals_sat   strict)
add_scp_chain_test(lin_not_equals_unsat strict)

# strict: all_different's per-pair selector is now named x[id][i_j] with cake's
# polarity (selector TRUE = "higher"), via the create_proof_flag(ConstraintID, role)
# overload -- the first consumer of the two-level aux-naming primitive (#354). The
# proof never references the selectors by name, so this is purely an OPB-definition
# conform and the encoding now byte-matches cake's.
add_scp_chain_test(all_different_unsat  strict)
add_scp_chain_test(all_different_sat    strict)

# strict: count, the second keystone consumer (#354) and a sterner test -- unlike
# all_different, its propagator references the per-position equality flag by name in
# its RUP steps. Its flags are now x[id][i][ge|le|eq] (created via the
# create_proof_flag_fully_reifying(ConstraintID, index list, annotation, ...) overload,
# with cake's [r]/[f] labelled halves), the equality is eq <=> ge & le (was ~gt & ~lt),
# and the sum is c[id][le|ge] -- matching cake's encoding exactly, so the propagator
# proof re-verifies against cake's OPB. count_sat also exercises the relative-line
# fix for lazily-introduced order literals (the chain-link `pol` was emitting absolute
# refs, which broke under cake's different constraint count -- the old count_sat gap).
# Domains are 0..2 (not 0..1) to stay off the binary {0,1} encoding (see below).
add_scp_chain_test(count_unsat  strict)
add_scp_chain_test(count_sat    strict)

# none (chain-only): element. cake uses the same lean strategy as the solver -- it
# reifies the per-entry equality (result = array[k]) on the *index variable's own*
# i[I][eqk] literal, no selector flags -- so there is nothing to conform on element's
# own side beyond labelling its equality halves. But byte-match is gated by a deeper,
# cross-cutting divergence: the solver's order/eq-literal *variable* encoding is lazy
# and lean (omits the trivial ge0/ge(n+1) boundary literals, defines eq0 <=> ~ge1,
# unlabelled), where cake's is eager and full (the whole ge ladder, eq0 <=> ge0 & ~ge1,
# all @i[I][...] labelled). That is shared variable-encoding machinery, not element --
# so element chain-verifies in workflow 2 (the solver's proof checks against cake's
# OPB; its eq literals are a semantically-equivalent subset of cake's) but cannot
# byte-match until that encoding is conformed. Tracked separately; gates the
# eq-literal / extensional family (element, among, table). SAT enumeration + UNSAT.
add_scp_chain_test(element_sat    none)
add_scp_chain_test(element_unsat  none)

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

# none (chain-only): inverse channeling chain-verifies; its clauses reuse the
# variables' own eq literals so the encoding lines up, but they're unlabelled vs
# cake, so no opbdiff byte-match.
add_scp_chain_test(inverse_sat  none)
