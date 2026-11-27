% Comparisons between a variable and a constant, reified, half-reified and
% negated (issue #1006). The reified ones reach int_le_reif and int_eq_reif
% with a literal on either side, `x != 0` forced through a negated implication
% reaches int_ne with a literal, and the comparisons between two variables in
% negated contexts reach two-term int_lin_*_reif rows. b1 to b4 compare x with
% itself, which the flattener decides, so they print as fixed Booleans.
var -2..2: x;
var -2..2: y;
var -2..2: u;
var bool: b1;
var bool: b2;
var bool: b3;
var bool: b4;
var bool: b5;
var bool: b6;
var bool: b7;
var bool: b8;

constraint b1 <-> (x <= x);
constraint b2 <-> (x < x);
constraint b3 <-> (x = x);
constraint b4 <-> (x != x);
constraint b5 <-> (1 <= x);
constraint b6 <-> (x < -1);
constraint b7 <-> (x != 0);
constraint b8 <-> (0 = y);
constraint not (y < u);
constraint not (x = u) \/ b5;
constraint b6 -> (u < y);
constraint not (b7 -> x < y);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(u) \([b1, b2, b3, b4, b5, b6, b7, b8])"];
