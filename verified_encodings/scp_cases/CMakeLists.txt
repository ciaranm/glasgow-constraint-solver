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

# strict: plus. The propagator's sum line is now the two labelled halves
# @c[id][le] (the Z >= a + b half) and @c[id][ge] (the Z <= a + b half), via the
# add_labelled_constraint equality overload, matching cake's encode_plus exactly
# (the bound lines already agreed -- plus is pure bit-sum, no eq/ge ladder, so it
# never hit #358). Domains are 0..2/0..6 (not 0..1) to stay off the binary {0,1}
# encoding (see below). SAT enumeration + UNSAT.
add_scp_chain_test(plus_sat     strict)
add_scp_chain_test(plus_unsat   strict)

# strict: minus, conformed exactly as plus -- @c[id][le] (the a - b <= c half,
# -a + b + c >= 0) and @c[id][ge] (a - b >= c, a - b - c >= 0). cake encodes
# `minus a b z` as the same a - b = z equality, so once labelled it byte-matches;
# minus is also pure bit-sum (no eq/ge ladder, no #358). The earlier "minus SAT
# trips a RUP" note no longer holds -- it was the count_sat lazily-introduced
# order-literal gap, since fixed by relative line refs -- so SAT enumeration now
# verifies too. Domains are non-binary (Z 0..2 unsat / 0..4 sat) to stay off the
# {0,1} boundary-line encoding. SAT enumeration + UNSAT.
add_scp_chain_test(minus_sat    strict)
add_scp_chain_test(minus_unsat  strict)

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

# none (chain-only): nvalue, the first consumer of the value-indexed `v[...]`
# aux-naming pattern (#354) -- completing the x / b / v family trio. cake encodes
# nvalue with a per-value occurrence flag v[id][v] <=> (some var = v) (its `Values`
# / `elm`) summed to n_values; the solver now matches that exactly, via the
# create_proof_flag_values_fully_reifying overload (v[id][v][r]/[f] halves) and the
# count-style c[id][le]/c[id][ge] sum. nvalue's *own* encoding byte-matches cake
# (the v[...] flags + sum), but unlike count it references *every* value's eq
# literal -- including the domain max, whose eq is defined against the ge(ub+1)
# boundary literal -- so it trips the same lazy-vs-eager variable-encoding gap as
# element (#358) and is chain-only for now. SAT enumeration + UNSAT.
add_scp_chain_test(nvalue_sat    none)
add_scp_chain_test(nvalue_unsat  none)

# none (chain-only): negative-domain nvalue. cake_pb_cp renders negative values
# in its labels verbatim (@v[id][-N], @i[X][eq-N]/[ge-N]); VeriPB-dev #191 settled
# that '-' is legal in @labels (it was already legal in variable names), so veripb
# now parses cake's OPB. The solver previously spelled negatives "minus", which
# made its proof reference i[X][eqminusN] while cake's OPB defined i[X][eq-N] -- a
# different variable to veripb, so the elaboration failed. The solver now renders
# negatives `-N` everywhere (eq/ge literals and v[...] flags), so its proof and
# cake's OPB agree on the variables and the chain verifies. Stays `none` because
# byte-match is still gated by the lazy-vs-eager variable encoding (#358), as for
# the positive nvalue cases above.
add_scp_chain_test(nvalue_neg_sat none)

# none (chain-only): reified equality, all four modes of ReifiedEquals -- the b[...]
# family's reified consumer (#354). cake's encode_equal (-iff) splits the equality
# into @c[id][le]/@c[id][ge] half-reified on the condition, adds per-side selectors
# b[id][gt]/b[id][lt] half-implying the strict comparisons (cake's gtv/ltv via
# cvar_imply, labelled @b[id][..][r]), and an @c[id][al1] at-least-one over lt, gt
# and the condition; the -if drops the selectors, and the not_equals_if FULLY reifies
# the selectors with the condition negated. The solver now matches each exactly (the
# @c[...]/@b[...][r]/[f] lines byte-match), reusing the create_proof_flag(ConstraintID,
# annotation) b[...] overload. Byte-match is gated only by the condition variable's
# eq-literal *definition* (@i[Z][eq1] via the ge ladder), the same lazy-vs-eager
# variable-encoding divergence as element (#358) -- so these chain-verify but register
# `none`. SAT enumeration over each reification mode (exercises both selector halves).
add_scp_chain_test(equals_if_sat        none)
add_scp_chain_test(equals_iff_sat       none)
add_scp_chain_test(not_equals_if_sat    none)
add_scp_chain_test(not_equals_iff_sat   none)

# none (chain-only): a {0,1} model variable is encoded as a single tautological
# line on i[v][b0], where cake emits two bound lines (lb + ub) on the same i[v][b0]
# -- so opbdiff sees cake's extra ub line ("only in B") and can't byte-match. The
# chain verifies regardless (the whole point of the relative-line work: VeriPB no
# longer pins the constraint count). Exercises the binary encoding both SAT
# (enumeration) and UNSAT.
add_scp_chain_test(binary_less_equal_sat  none)
add_scp_chain_test(binary_equals_unsat    none)

# none (chain-only): logical and/or chain-verify but don't byte-match. They use
# {0,1} variables, so they diverge on cake's eager per-variable lb/ub boundary
# lines (the binary-encoding subcase of #358, as for the binary_* cases above) --
# not a missing label, so a relabel alone wouldn't byte-match them.
add_scp_chain_test(and_sat      none)
add_scp_chain_test(or_sat       none)

# none (chain-only): parity (ParityOdd). cake's `parity (Xs) Y` encodes Y = XOR(Xs);
# the solver's bare odd-parity XOR(Xs)=1 is written as `parity (Xs) 1`. cake builds
# the same chain of arc-consistent XOR gadgets the solver does (seed + 4 clauses per
# input + final pin), and the propagator's RUP inferences verify against it directly
# (no pol scaffolding) -- it only fires with <=1 input free, so unit propagation
# threads through the chain. Inputs are {0,1}, so it diverges from cake only on the
# binary lb/ub boundary lines (the #358 subcase, as for and/or) -> none, not strict.
# parity_unsat forces the conflict over *free* vars (parity gives A!=B, equals gives
# A=B) rather than fixed domains, which would drag in the ge0 ladder for the pinned
# variable (also #358). SAT enumeration + UNSAT.
add_scp_chain_test(parity_sat    none)
add_scp_chain_test(parity_unsat  none)

# none (chain-only): inverse channeling chain-verifies; it references the
# variables' own eq/ge literals, so it trips the same lazy-vs-eager variable-
# encoding gap as element (#358) (cake's full ge0 ladder + eq0 <=> ge0 & ~ge1),
# and its clauses are unlabelled vs cake -- so no opbdiff byte-match yet.
add_scp_chain_test(inverse_sat  none)

# none (chain-only): `in` (membership). cake_pb_cp's parser takes the candidate
# list first then the variable -- (id in (values...) var) -- and the solver now
# emits that order (it previously emitted the variable first, which cake rejected
# outright). A constant candidate contributes a fixed eq literal and a variable
# candidate a reified selector, summed at-least-one; that's the same lean shape
# cake uses, so it chain-verifies. Byte-match stays gated by the eq-literal
# variable encoding (#358), as for the element / nvalue family. in_var exercises
# a variable candidate (V == W) alongside a constant; in_unsat forces the domain
# empty (Y in {5} with Y in 0..3).
add_scp_chain_test(in_const_sat  none)
add_scp_chain_test(in_var_sat    none)
add_scp_chain_test(in_unsat      none)
