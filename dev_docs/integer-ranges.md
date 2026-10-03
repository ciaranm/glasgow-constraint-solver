# Integer ranges: what the solver accepts, and what it promises

`Integer` is a checked 64-bit integer, and the solver does not support
arbitrary precision. Instead there is one range, `S`, which is
`Integer::min_bounded_value()` .. `Integer::max_bounded_value()`, an eighth of
the machine range in each direction (−(2⁶⁰ − 1) .. 2⁶⁰ − 1). The rule:

> Given inputs in `S`, the solver behaves. Given anything outside `S`, it throws
> `IntegerOverflow`.

This page says what counts as an input, what "behaves" means, why `S` is the
size it is, and what a constraint has to do to keep its side of the bargain.

## What has to lie in `S`

Every `Integer` a caller hands the solver:

- **A variable's declared domain.** `State::allocate_integer_variable_with_state`
  checks it, which covers every route to a variable, including the auxiliaries
  constraints create for themselves.
- **A constant.** `ConstantIntegerVariableID`'s constructor checks it, so `42_c`,
  `constant_variable()` and the constant folding in the view operators all do.
- **A view's offset.** `ViewOfIntegerVariableID`'s constructor checks it. A view
  is always flattened to `±x + c`, so composing views, as in `(x + a) + b`,
  checks the combined `c = a + b`; it does not matter how the view was built,
  only that its single offset lies in `S`. A view's values can therefore reach
  twice as far as a variable's, about ±2⁶¹: one extra bit, and never more.
- **Every constraint parameter**: a coefficient, a tuple value, a chain value, a
  distance, a capacity, and so on. Each constraint checks its own, with
  `innards::require_bounded`, when it is constructed. See
  [Obligations on a constraint](#obligations-on-a-constraint).

`S` is symmetric, one value short of an eighth of two's complement at the
bottom, so that negating an input never leaves it. That matters because the
solver negates things the caller never sees: `maximise(x + c)` is stored as
`−x − c`, and with `min_bounded_value()` at −2⁶⁰ it would have thrown for `c`
at the bottom of the range.

## What "behaves" means

For inputs in `S`, never a wrong answer, undefined behaviour, a crash, a
truncated proof, or a proof that VeriPB rejects. Beyond that it depends on the
constraint:

- **A constraint that only compares or matches values** (`Lex`, `Table`,
  `Element`, `AllDifferent`, `ValuePrecede`, `MinDistance`, the comparisons, …)
  must give the right answer and a verifying proof for every in-range input,
  including views at the full one-bit reach.
- **A constraint that does arithmetic on values** (`Linear`, `Multiply`, `Power`,
  `Knapsack`, the scheduling energies, …) may also throw `IntegerOverflow` when a
  value it genuinely needs does not fit in an `Integer`. A product of two
  variables near the edges of `S` is the obvious case: that is a limit of 64-bit
  arithmetic, not a bug. Throwing is the only acceptable alternative to the
  right answer.

Throwing *because the input was out of range* should happen as early as
possible, at construction or at the latest in `prepare()`, so that nothing has
been searched or written to a proof yet. The proof writer turns an overflow
while rendering a row into `IntegerOverflow` with a message naming the likely
cause; reaching that from in-range inputs means a comparison-only constraint has
a bug, or an arithmetic constraint has hit its genuine limit.

## Why an eighth

The proof model is what sets the size. A half-reified row's reification constant
is the sum of the positive contributions of *every* term, so a row relating two
variables needs room for both, and the constant is negated again when the row is
rendered in `>=` form, where the most negative machine integer has no negation.
That costs two bits. The domain cap used to be a quarter of the machine range,
which was measured: `LessThan`, `Plus` and `AllDifferent` all write their model
there, and at a half all three abort part-way through emission (issue #852).

Views take the third bit. A view gets a bit vector of its own the first time a
model row uses it (#1208), and a view near −2⁶² gets a sign bit of weight −2⁶²
and positive bits worth almost as much again. With the cap at a quarter and a
view's offset allowed the same range, `LessThan{x + A, u + B}`,
`AllDifferent` over three such views and `LexGreaterEqual{{x + A}, {y + A}}`
(`A` and `B` the ends of the range, `x`, `y` and `u` near them) all throw while
writing the model, though each solves correctly without proofs. At an eighth,
all three verify, as does `Plus` over the same views.

The consequence that is easy to miss: a variable declared over the whole of `S`
is narrower than it used to be. `fzn-glasgow` gives a FlatZinc `var int` with no
declared domain exactly `S`, so that default lost a bit too.

## Obligations on a constraint

- **Check every `Integer` parameter** with `innards::require_bounded(value,
  "a description")` in the constructor. Parameters that become variables or
  constants on the way in (a constant array passed through
  `as_constant_variables`, say) are already checked.
- **Do not narrow the rule by dropping inputs.** An out-of-range tuple value
  could never match a variable, but it could match a view (#1117's review), and
  silently dropping it hides a caller's mistake. Throw instead.
- **Test the edges.** A constraint's tests should include domains at both ends
  of `S`, views with offsets at both ends of `S` and both signs, and parameters
  at both ends of `S`, with proofs. That is where every bug in this area has
  been.

The parameter checks are being added constraint by constraint. Until a
constraint has its own, an out-of-range parameter may still throw late, or not
at all.
