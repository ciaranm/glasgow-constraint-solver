% Linear constraints as a model writes them (issue #1006): very unequal
% coefficients, a variable repeated, which the flattener merges into one term
% with coefficient 2, and reified, half-reified and negated rows. The flattener
% emits a half-reification as a full one plus a clause, and a negated row as the
% opposite reified row, so all of these reach int_lin_eq_reif, int_lin_le_reif
% or int_lin_ne_reif, several of them over two unit-coefficient terms, which
% the reader recovers only in the non-reified forms.
var -3..3: x;
var -3..3: y;
var 0..3: z;
var bool: b;
var bool: c;
var bool: d;
var bool: e;

constraint 1000 * x + y >= -2001;
constraint x + y + x <= 3;
constraint b <-> (2 * x + 3 * y <= 1);
constraint c -> (2 * x - 3 * z = 1);
constraint d <-> not (x + 2 * y != 1);
constraint not (x - y + z = 2) \/ e;
constraint e -> (x - 3 * z >= -4);
constraint (x - y < 2) -> b;

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(z) \(b) \(c) \(d) \(e)"];
