% Two-term unit-coefficient equalities and disequalities over one variable
% twice (issue #1006), called directly so the flattener passes them through.
% The reader recovers each as Equals or NotEquals between a variable and a view
% of itself: `x + x = 2` is Equals{x, -x + 2}, so x = 1; `y + y != 0` is
% NotEquals{y, -y}, so y != 0; `y - y != 0` is NotEquals{y, y}, which would be
% unsatisfiable, so it is reified and b is always false; `-z - z = -4` puts
% both coefficients at -1. A sign slip in the normalisation moves each of these
% to a different value.
var -3..3: x;
var -3..3: y;
var -3..3: z;
var bool: b;

constraint int_lin_eq([1, 1], [x, x], 2);
constraint int_lin_ne_reif([1, -1], [y, y], 0, b);
constraint int_lin_eq([-1, -1], [z, z], -4);
constraint int_lin_ne([1, 1], [y, y], 0);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(z) \(b)"];
