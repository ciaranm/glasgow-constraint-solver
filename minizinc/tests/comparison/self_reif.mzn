% Each comparison builtin called directly on one variable twice (issue #1006),
% which the flattener passes through unchanged: int_le_reif(x, x, b1) and its
% siblings, a non-reified int_le(y, y), and two-term reified linear rows over
% [x, x] and [y, y]. A propagator that assumes its operands are distinct reads
% `x <= x` as a constraint between two variables and can get either polarity of
% the reification wrong. int_eq(y, y) is in the model too, but the flattener
% drops it.
var -2..2: x;
var -2..2: y;
var bool: b1;
var bool: b2;
var bool: b3;
var bool: b4;
var bool: b5;
var bool: b6;

constraint int_le_reif(x, x, b1);
constraint int_lt_reif(x, x, b2);
constraint int_eq_reif(x, x, b3);
constraint int_ne_reif(x, x, b4);
constraint int_le(y, y);
constraint int_eq(y, y);
constraint int_lin_le_reif([1, -1], [x, x], -1, b5);
constraint int_lin_eq_reif([2, -1], [y, y], 0, b6);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \([b1, b2, b3, b4, b5, b6])"];
