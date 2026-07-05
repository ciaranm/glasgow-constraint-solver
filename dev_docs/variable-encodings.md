# Variable encodings: state, OPB, and proof

There are several ways to bring an integer variable (or a Boolean flag) into
existence, and they differ along two independent axes: whether the variable has
**solver state** (a domain that propagation reads and writes) and whether its
encoding is **asserted in the OPB** (`.opb`) or only **introduced inside the
proof** (`.pbp`). This document is the map of those mechanisms, so you can pick
the right one and see that they are complementary rather than duplicated.

For the state side in isolation — the `IntegerVariableID` family, the `State`
class, epochs — see [state-and-variables.md](state-and-variables.md). This
document is about the *proof-encoding* side and how it composes with state.

## The mechanisms

| Mechanism (how to create) | User-visible? | Has state? | In OPB? | Usable in PBP? |
|---|---|---|---|---|
| `Problem::create_integer_variable` | **Yes** | Yes | Yes (`@i[v][lb/ub]`) | Yes |
| `State::allocate_integer_variable_with_state` (alone) | No | Yes | No | No¹ |
| ` … ` + `ProofModel::set_up_integer_variable` | No | Yes | Yes (`@i[v][lb/ub]`) | Yes |
| ` … ` + `ProofModel::register_state_variable_bits_in_proof` + `ProofLogger::introduce_bits_of` | No | Yes | No | Yes² |
| `ProofModel::create_proof_only_integer_variable` (`Bits`/`DirectOnly`) | No | No | Yes (unlabelled) | Yes |
| `ProofModel::create_proof_only_integer_variable` + `CakeBitNaming` | No | No | No | Yes |
| `ProofModel::create_proof_only_integer_variable_in_proof` + `ProofLogger::introduce_bits_of` | No | No | No | Yes² |
| `ProofModel::create_proof_flag` / `_reifying` / `_fully_reifying` | No | No | reification only³ | Yes |

¹ A state variable with no proof encoding is fine only if it is *never referenced
in a proof step* — in particular never narrowed by a logged inference. Give it an
encoding (one of the two rows below it) the moment it appears in the proof.

² Registered means the bits are *nameable*; the variable only becomes *meaningful*
once its `introduce_bits_of` (or lazy-atom channel) runs — see "Ordering" below.

³ A bare `create_proof_flag` asserts nothing. `create_proof_flag_reifying` emits
its reification at a `ProofLevel` (in the PBP); the position/value-indexed
`create_proof_flag_fully_reifying` emits labelled reification lines to the OPB.

## The two axes, and the one primitive underneath

**Has state?** is set by *who allocates the ID*: `allocate_integer_variable_with_state`
(and `Problem::create_integer_variable`, which wraps it) mint a
`SimpleIntegerVariableID` with a domain in `State`; `create_proof_only_*` mint a
`ProofOnlySimpleIntegerVariableID`, which has no state and exists only for the
proof.

**In OPB?** is set by *which encoder you call*, and every path shares one private
primitive:

- `register_bits_variable_encoding(id, lo, hi, name, [cake])` — allocate and name
  the bit literals and record the bounds, **emit nothing to the OPB**.
- `set_up_bits_variable_encoding` = `register_bits_variable_encoding` **plus** the
  `>= lo` / `<= hi` bound lines in the OPB (labelled `@i[name][lb/ub]` for a state
  variable, unlabelled for a proof-only one).

So "set up" is exactly "register + assert bounds in the OPB". `set_up_integer_variable`,
`create_proof_only_integer_variable`, `register_state_variable_bits_in_proof`, and
`create_proof_only_integer_variable_in_proof` are all thin wrappers choosing (a)
whether to mint a fresh proof-only ID or take an existing state ID, and (b) whether
to go through `set_up_*` (OPB) or `register_*` alone (in-proof). The `CakeBitNaming`
overloads are the same register-only path with cake's `x[]/v[]` bit names instead
of the default `i[name][b]` / `p[index][b]`.

That is why the two "…`_in_proof`" rows and `register_state_variable_bits_in_proof`
look almost identical: they *are* the same primitive, differing only in the state
axis. `register_state_variable_bits_in_proof` is the state-backed analogue of
`create_proof_only_integer_variable_in_proof` — it fills the `(has state, not in
OPB)` cell that was otherwise empty, not a duplicate of an existing function.

## Why "not in OPB" is a first-class option

The `.pbp` proof is checked against **two** OPBs: our own (workflow 1) and the one
`cake_pb_cp` re-derives from the `.scp` (workflow 2, the chain — see
[workflow2_testing.md](workflow2_testing.md)). A proof that references a variable
only *our* OPB defines will fail against cake's. So any variable that is ours alone
— internal auxiliaries with no counterpart in cake's encoding — must **not** be an
OPB axiom; it must be introduced *inside* the proof as a conservative extension
(`introduce_bits_of`, which defines the variable equal to a linear form in `2m`
redundancy steps), so the proof stays valid against either OPB. `In OPB = No` is
what makes a variable **chain-portable**.

For a pure proof helper (a magnitude, a rank, a witness) that is naturally
`create_proof_only_integer_variable_in_proof`. The wrinkle that motivated
`register_state_variable_bits_in_proof`: an auxiliary that must *also* drive
propagation. `Divide`/`Modulus` reuse `mult_bc::propagate`, which reads
`state.bounds(w)` on the product `w = q·y` — so `w` needs real state — yet cake's
divide OPB has no `w`, so `w`'s encoding must be in-proof-only. That is the
`(has state, not in OPB)` cell, and neither `set_up_integer_variable` (state but in
OPB) nor `create_proof_only_integer_variable_in_proof` (in-proof but no state)
provides it.

## Footguns for an in-proof-encoded state variable

The two in-proof rows share a rule — the variable is meaningless until introduced
— and the state-backed one adds a second:

- **Ordering.** `introduce_bits_of` must run *before* any proof step references the
  variable — and for a state variable, before the first *logged inference narrows
  it*, because the eager tracker will try to justify that bound change over bits
  whose meaning is not yet established. Do the introduction in an
  `install_initialiser` (runs once at proof start, before propagation); see
  `disjunctive.cc` for the pattern and the shared cache for the returned lines.
- **Boundary-literal derivability.** A free bit-sum with no OPB bound lines cannot
  RUP-derive its own `v >= lo` / `v <= hi` boundary literals. If the proof needs
  them, register the variable's bounds as not-trivially-derivable
  (`note_bounds_not_trivially_derivable`, as ArgSort's free signed bit-sums do) and
  derive the bounds once, explicitly, from the introduction.

## Rule of thumb

- User model variable → `Problem::create_integer_variable`.
- Internal aux that appears in *our* OPB and needs propagation →
  `allocate_integer_variable_with_state` + `set_up_integer_variable`.
- Internal aux that must be **chain-portable** and needs propagation →
  `allocate_integer_variable_with_state` + `register_state_variable_bits_in_proof`,
  introduced with `introduce_bits_of` in an initialiser.
- Pure proof helper → `create_proof_only_integer_variable_in_proof` (chain-portable)
  or `create_proof_only_integer_variable` (asserted in our OPB), `CakeBitNaming` when
  its bits must match cake's.
- A proof-only Boolean → `create_proof_flag` and its reifying variants.
