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

# strict: all_equal. cake labels each consecutive-pair equality's two halves
# @c[id][<i>le] (vars[i+1] - vars[i] >= 0) and @c[id][<i>ge] (vars[i] - vars[i+1]
# >= 0); the solver's chain-step equality now emits those labels via the
# add_labelled_constraint equality overload (was an unlabelled add_constraint).
# all_equal is pure comparison (no eq/ge ladder), so labelling alone byte-matches
# cake -- no #358 involvement. The proof never references the lines by name (the
# propagator prunes by RUP), so it's a pure OPB-definition rename. Domains stay
# off the {0,1} boundary (sat 0..3; unsat uses disjoint 0..2 / 3..5).
add_scp_chain_test(all_equal_sat    strict)
add_scp_chain_test(all_equal_unsat  strict)

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

# none (chain-only): circuit. The solver's writer already emits cake's shape
# (id circuit (succ...)); its embedded all_different sub-encoding even matches
# cake (the #355 x[id][i_j] conform), but the Hamiltonicity / position-variable
# layer is encoded differently (the solver's p[N_posK] position vars) and the
# successor eq/ge literals trip #358 -- so it chain-verifies but is far from
# byte-match. circuit_sat enumerates the two 3-node cycles; circuit_unsat
# confines successors to {0,1} so two of the four nodes are unreachable.
add_scp_chain_test(circuit_sat    none)
add_scp_chain_test(circuit_unsat  none)

# none (chain-only): array_min / array_max. cake now FULLY reifies the per-value
# selector x[id][i] <=> (var = result) (it used to half-reify, which left the
# at-least-one unpinnable at a solution -- that fix unblocks enumeration). The
# solver's encoding matches cake's exactly once its selector is named x[id][i]
# (the create_proof_flag(ConstraintID, {i}) two-level form, as for all_different)
# instead of the old f[idx][arrayminmax] -- the propagator's RUP steps reference
# it by name, so the names must agree for enumeration to verify. Stays none (the
# eq/ge literal variable encoding still diverges, #358).
add_scp_chain_test(array_min_sat    none)
add_scp_chain_test(array_max_sat    none)
add_scp_chain_test(array_min_unsat  none)

# none (chain-only): lexicographic comparison. cake reuses the scalar comparison
# keywords over two lists -- lex_{greater,less}_{than,equal}[_if|_iff] -- and the
# solver now emits that (the or-equal forms became lex_greater_equal /
# lex_less_equal, not ..._than_equal, and the reification condition is the
# (var op val) triple cake expects). The solver's prefix-equality and decision
# flags are renamed to cake's x[id][i][pref] and x[id][i][dec] (the greater
# direction) / x[id][i][inc] (the less direction), via the
# create_proof_flag(ConstraintID, {i}, stem) form -- the propagator's RUP steps
# reference them by name, so the names must agree for enumeration to verify. The
# single pref set is shared across both directions (as cake does), so the
# fully-reified _iff verifies too -- each direction redundantly defines the
# shared pref under its half of the condition. Stays none (the operands' eq/ge
# literal encoding still diverges, #358). All four directions verify plain (sat +
# unsat), half-reified (_if) and fully-reified (_iff). unsat confines the two
# lists to disjoint ranges so the comparison cannot hold; the reified cases
# enumerate both branches of the condition.
add_scp_chain_test(lex_greater_than_sat       none)
add_scp_chain_test(lex_greater_than_unsat     none)
add_scp_chain_test(lex_greater_equal_sat      none)
add_scp_chain_test(lex_greater_equal_unsat    none)
add_scp_chain_test(lex_less_than_sat          none)
add_scp_chain_test(lex_less_than_unsat        none)
add_scp_chain_test(lex_less_equal_sat         none)
add_scp_chain_test(lex_less_equal_unsat       none)
add_scp_chain_test(lex_greater_than_if_sat    none)
add_scp_chain_test(lex_less_equal_if_sat      none)
add_scp_chain_test(lex_greater_than_iff_sat   none)
add_scp_chain_test(lex_greater_equal_iff_sat  none)
add_scp_chain_test(lex_less_than_iff_sat      none)
add_scp_chain_test(lex_less_equal_iff_sat     none)

# none (chain-only): global cardinality. The solver's writer already emits cake's
# keywords (bounds/gac globalcardinality[closed]) over (vars)(values)(counts);
# the encoding is the per-value count constraint Sum_i (x_i = values[j]) =
# counts[j] (the closed forms add an at-least-one over the cover values per
# variable). cake defines the eq/ge literals eagerly, so it chain-verifies but
# does not byte-match (#358). The open (sat + unsat) and GAC (sat + unsat) cases
# verify, as does closed enumeration (closed_sat confines 0..2 vars to {0,1}).
# closed_unsat is omitted: its refutation derives the contradiction through the
# eq-literal ladder, which is exactly where the lazy-vs-eager encoding (#358)
# diverges, so that proof shape does not yet line up against cake's OPB.
add_scp_chain_test(global_cardinality_sat         none)
add_scp_chain_test(global_cardinality_unsat       none)
add_scp_chain_test(global_cardinality_closed_sat  none)
add_scp_chain_test(global_cardinality_gac_sat     none)
add_scp_chain_test(global_cardinality_gac_unsat   none)

# none (chain-only): regular (the sequence of variables is a word accepted by a
# finite automaton). The writer emits cake's shape -- (vars...) nstates
# ((edges-of-0) (edges-of-1) ...) (finals...), each edge (symbol target) -- and
# the "in state q at position i" flag is named x[id][i_q][st] (the
# create_proof_flag(ConstraintID, {i, q}, "st") form), matching cake, so the
# propagator's RUP steps over the state flags line up against cake's OPB. The
# transition literals still diverge (cake spells them over eager eq-literals, we
# over the lazy bits, #358), but the chain verifies anyway: cake defines the
# bit<->eq linkage, so the bit-basis RUP bridges to cake's eq-basis clauses.
# sat is a parity DFA (an even number of 1s), unsat an automaton whose only
# accepting state is unreachable in three steps, ternary_sat a sum-mod-3 DFA over
# 0..2 -- a wider eq/ge ladder, exercising the bridge off a binary domain.
add_scp_chain_test(regular_sat          none)
add_scp_chain_test(regular_unsat        none)
add_scp_chain_test(regular_ternary_sat  none)

# none (chain-only): disjunctive / disjunctive2d. The tasks [start, start+length)
# (resp. rectangles [x,x+w) x [y,y+h)) pairwise do not overlap. The solver's
# before flags are named to match cake -- x[id][i_j][bf] (the "task i finishes
# before task j" ordering), x[id][i_j][bx]/[by] (the per-axis 2D orderings),
# x[id][i][zw]/[zh] (zero-size escapes). These were previously blocked from the
# chain because cake only HALF-reified its before flags (flag -> ordering, not the
# converse), whereas the solver full-reifies by design rule and falsifies a before
# flag from the variable bounds by unit propagation -- a RUP step that is
# underivable against a half-reified OPB. cake_pb_cp now FULL-reifies the before
# flags (cbimply_var, the biconditional), so that converse is present and the chain
# verifies. Stays none: the ordering linear constraints reference the start/size
# bit encodings, which still diverge from cake's eager variable encoding (#358).
# sat enumerates the non-overlapping placements; unsat is a pigeonhole (more unit
# tasks than slots / two width-2 rectangles that cannot separate in a 2x2 area).
add_scp_chain_test(disjunctive_sat        none)
add_scp_chain_test(disjunctive_unsat      none)
# Variable-duration disjunctive: end_i = s_i + l_i is introduced as an in-proof
# conservative extension (ProofLogger::introduce_bits_of), not an OPB axiom, so
# the proof carries its own end definition and chains against cake's OPB (which
# has no end variable). This is what constant-duration cases never exercise.
add_scp_chain_test(disjunctive_var_sat    none)
add_scp_chain_test(disjunctive2d_sat      none)
add_scp_chain_test(disjunctive2d_unsat    none)
# Variable-size disjunctive2d: same in-proof end = pos + size conservative
# extension as disjunctive_var, per axis (see introduce_bits_of).
add_scp_chain_test(disjunctive2d_var_sat  none)

# none (chain-only): cumulative. Tasks [start, start+length) each occupy `height`
# of a shared resource; at every time point the total height of active tasks is at
# most `cap` (lengths, heights and cap may each be a variable or a constant). cake
# uses a time-table encoding: over a global time window it reifies, per (task,
# time), before (start <= t), after (start + length > t) and active = before &
# after, pins a proof-only contribution bit-sum to the height when active and 0
# otherwise, and sums the contributions <= cap at each time. The solver's own
# propagator is time-table consistent and emits a structurally matching proof --
# the same before / after / active reifications -- so conforming is a naming-only
# change: define_proof_model names the flags v[id][i_t][cb] / [ca] / [cact] (cake's
# value-indexed family, via create_proof_flag_values_fully_reifying) instead of the
# old f[..][cumbefore/cumafter/cumactive]. The solver's per-task time window is a
# subset of cake's global one, so every flag the proof cites is one cake also
# defines, and the proof's RUP steps over them resolve against cake's OPB. No
# propagator change (it holds the flag handles, whose names the rename updates).
# Stays none: the start / size bit encodings still diverge from cake's eager
# variable encoding (#358). sat enumerates the placements that keep every slot
# within capacity (cumulative_var_sat uses variable heights, exercising the
# contribution path); unsat forces more load into a slot than the capacity allows.
add_scp_chain_test(cumulative_sat         none)
add_scp_chain_test(cumulative_var_sat     none)
add_scp_chain_test(cumulative_unsat       none)
