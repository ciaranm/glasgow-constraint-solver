# Issue #254 audit: degenerate (empty / all-constant) constraint argument cases

Branch: `audit/degenerate-constraint-cases`. Oracle: VeriPB 3.0.2 (`--prove` on).

Goal per constraint: (1) all-constant args → reduces to true/false check, both
tautology and contradiction directions; (2) empty / single-element collections;
(3) mixed const+var folding. Assert the **full** solution set, verify the proof.

Status legend: ✅ done & passing · 🐛 bug fixed + test · ⚠️ deferred (see report) · — n/a

## Outcome

**Every constraint family in `gcs/constraints/` now has degenerate-case
coverage** (all-constant, empty, single-element, mixed), run with proofs on so
VeriPB validates each. The audit surfaced **2 real bugs**, both fixed with
regression tests:

- **Lex with an empty operand** — proof-model nullopt dereference (`ProofError:
  can't find literals for flag`), latent until `--prove`.
- **Regular over an empty sequence** — wrong SAT (soundness): the empty word was
  accepted regardless of whether the initial state is final.

Where genuine `ConstantIntegerVariableID`s are accepted by the test harness (the
`variant<int,…>` data tests) they were used directly; where the harness only
takes `pair<int,int>` (or the constraint rejects constants, e.g. SmartTable),
singleton-domain variables and/or focused tests exercise the all-fixed path.
Nothing was deferred. One PR, one commit per family (fixes bundled with their
tests for bisectability).

| Family | Files | Status | Notes |
|---|---|---|---|
| linear | linear_constant_test.cc (#253) | ✅ pre-existing | extend with inequalities/empty? |
| abs | abs_test.cc | ✅ | all-constant (taut+contra), singleton-domain, mixed rows added; proofs verify |
| comparison | comparison_test.cc | ✅ | genuine all-constant operands (taut+contra), all modes incl _if/_iff |
| equals | equals_test.cc | ✅ | genuine all-constant operands (taut+contra) across Equals/NotEquals + reified |
| plus/minus | plus_minus_test.cc | ✅ | fully all-constant ternary (taut+contra for both Plus and Minus) |
| mult_bc | mult_bc_test.cc | ✅ | all-fixed singleton operands (taut+contra incl negatives, zero) |
| arithmetic | arithmetic_test.cc | ✅ | all-fixed operands across Plus/Minus/Times/Div/Mod/Power (taut+contra) incl div/mod by fixed zero → UNSAT |
| all_different | all_different_test.cc | ✅ | all-const 6-tuples + focused empty/single/all-const collection test (empty=vacuous SAT) |
| all_different_except | all_different_except_test.cc | ✅ | empty/single pre-existing; added all-fixed taut+contra (dup-of-excluded, distinct, empty excluded) |
| symmetric_all_different | symmetric_all_different_test.cc | ✅ | empty/single pre-existing; added fully all-fixed involution taut+contra |
| all_equal | all_equal_test.cc | ✅ | singleton all-const rows + focused empty/single/genuine-const collection test (empty=vacuous SAT) |
| among | among_test.cc | ✅ | empty array, empty value-set, single, all-const (taut+contra); proofs verify |
| at_most_one | at_most_one_test.cc | ✅ | empty/single pre-existing; added fully all-fixed taut+contra |
| count | count_test.cc | ✅ | empty/single/all-const arrays + genuine const how_many/voi (taut+contra); proofs verify |
| element | element_test.cc | ✅ | empty 1D+2D arrays (var/const/2d) → UNSAT; all-fixed taut+contra incl out-of-range index |
| global_cardinality | bounds_/gac_global_cardinality_test.cc | ✅ | both bounds+gac: empty vars (open+closed), empty value set, single value, all-const vars/counts (taut+contra) |
| in | in_test.cc | ✅ | empty value/var lists (all overloads → UNSAT) + fixed-var taut+contra |
| increasing | increasing_test.cc | ✅ | all-const chains (taut+contra per variant) + mixed; empty/single pre-existing |
| inverse | inverse_test.cc | ✅ | already strong (empty/single/const-pins); added fully all-const taut+contra |
| knapsack | knapsack_test.cc | ✅ | empty item list (sum=0 → SAT/UNSAT, verifies), single item, all-fixed taken vars (taut+contra) |
| lex | lex_test.cc | 🐛 | FIXED nullopt-deref in proof model when one operand empty (n==0 & equal_prefix_satisfies) → 'can't find literals for flag'. Added empty/all-fixed rows; all modes verify |
| logical | logical_test.cc | ✅ | genuine empty array (And/Or), all-const operands + reif both directions (taut+contra) |
| min_max | min_max_test.cc | ✅ | all-const + single-const arrays (taut+contra); empty array → clean InvalidProblemDefinitionException (focused test) |
| n_value | n_value_test.cc | ✅ | all-const arrays + genuine const result (taut+contra); empty/single pre-existing; proofs verify |
| parity | parity_test.cc | ✅ | already strong; added genuine single/all-const rows (taut+contra) |
| regular | regular_test.cc | 🐛 | FIXED wrong-SAT on empty sequence (propagator looped over 0 positions, never checked initial state acceptance). Added empty/single-fixed/all-fixed/mixed rows; verify |
| seq_precede_chain | seq_precede_chain_test.cc | ✅ | variant-supporting; empty pre-existing; added single + fully all-const (taut+contra) |
| smart_table | smart_table_test.cc | ✅ | new 'degenerate' mode: empty tuple list (UNSAT), all-fixed match/nomatch, single-var; SmartTable rejects genuine constants by design (singleton vars used) |
| sort / arg_sort | sort_test.cc, arg_sort_test.cc | ✅ | empty arrays (vacuous SAT), single, all-fixed (taut+contra for Sort; unique perm for ArgSort, 0/1-based) |
| table / negative_table | table_test.cc, negative_table_test.cc | ✅ | empty tuple-list (Table UNSAT) / empty forbidden-list (NegTable all-allowed) pre/added; all-fixed vars taut+contra + mixed |
| value_precede | value_precede_test.cc | ✅ | empty/single/all-const vars (taut+contra); empty/single chain pre-existing |
| circuit | circuit_test.cc (+scenarios) | ✅ | added n=1 (self-loop, minimal circuit) + n=2 (unique 2-cycle); verify. n=0 N/A (meaningless + oracle indexes visited[0]) |
| cumulative | cumulative_test.cc | ✅ | empty active-task list (all zero len+ht), all-fixed feasible/overload (taut+contra); single/zero pre-existing |
| disjunctive / 2d | disjunctive_test.cc, disjunctive_2d_test.cc | ✅ | both strict+nonstrict: empty task/rect list (vacuous SAT), single rect, all-fixed abutting/overlapping (taut+contra) |

## Deferred (non-obvious) bugs

(none yet)

## Fixed bugs

### Lex with an empty operand — proof-model nullopt dereference (FIXED)
`build_lex_direction_encoding` (gcs/constraints/lex.cc) built the at-least-one
disjunction as `... + 1*(*prefix_equal->at(n))`. When `n = min(|vars_1|,|vars_2|)
== 0` (one operand empty, e.g. `LexGreaterThan([x], [])`) and
`equal_prefix_satisfies` holds, `prefix_equal->at(0)` is the deliberately-`nullopt`
empty-prefix placeholder (the always-TRUE flag), so `*` dereferenced an empty
optional (UB) and registered a garbage proof flag. With proofs on this aborted
with `ProofError: can't find literals for flag`; without proofs the solver gave
the right answer, so it was latent until `--prove`. Since the empty prefix is
trivially equal, the disjunction is satisfied unconditionally, so the fix skips
the constraint when `n == 0 && equal_prefix_satisfies`. Both empty-empty (strict
→ UNSAT, non-strict → SAT) and nonempty-vs-empty now verify across all
plain/reified modes. Regression rows added to lex_test.cc.

### Regular over an empty sequence — wrong SAT (FIXED)
`propagate_regular` (gcs/constraints/regular/regular.cc) does all its work in
loops over the per-position `states_supporting` array, whose length is the
number of variables. With an empty variable list those loops never run, so the
propagator never enforced that the empty word is accepted only when the initial
state (0) is itself final. `Regular([], ..., final_states)` therefore reported
the empty assignment as a solution even when `0 ∉ final_states` — a wrong-SAT
(soundness) bug, independent of proofs. Fix: when `vars.empty()`, infer a RUP
contradiction iff `0 ∉ final_states` (the proof model already pins
state_at_pos[0] to state 0 with an exactly-one and requires a final state, so
the contradiction is RUP-derivable). Empty-accepted (1 solution),
empty-rejected (UNSAT), single-fixed, all-fixed and mixed rows added to
regular_test.cc; all verify under VeriPB.
