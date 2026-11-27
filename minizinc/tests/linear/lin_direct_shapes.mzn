% Linear builtins called directly, which reaches shapes the flattener would
% otherwise tidy away (issue #1006): a zero coefficient, which it keeps in a
% two-term row, so the two-term recovery has to decline it rather than divide
% by it; a single term, reified; an integer literal among the variables, which
% the flattener keeps in an equality, so the recovery posts Equals{2, w + 1},
% and turns into a single-term row in a disequality; and one variable twice in
% a two-term unit-coefficient row, which is exactly the shape the recovery
% rewrites into a comparison between a variable and a view of itself:
% `x + x <= 1` becomes LessThanEqual{x, -x + 1}. The flattener creates such
% rows itself when it unifies two variables. int_lin_le([1, -1], [2, z], 3) and
% int_lin_eq([1, -1], [z, z], 0) are folded away, and are here to say so.
var -3..3: x;
var -3..3: y;
var -3..3: z;
var -3..3: w;
var bool: b;
var bool: c;

constraint int_lin_le([0, 1, 1], [x, y, z], 1);
constraint int_lin_ne([0, 1], [x, y], -1);
constraint int_lin_le([1, 0], [y, x], 2);
constraint int_lin_le_reif([2], [x], 1, c);
constraint int_lin_le([1, -1], [2, z], 3);
constraint int_lin_ne([1, -1], [z, 1], 0);
constraint int_lin_le([1, 1], [x, x], 1);
constraint int_lin_ne([1, 1], [y, y], 2);
constraint int_lin_eq([1, -1], [z, z], 0);
constraint int_lin_le_reif([1, 1], [x, x], -2, b);
constraint int_lin_eq([1, -1], [2, w], 1);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(z) \(w) \(b) \(c)"];
