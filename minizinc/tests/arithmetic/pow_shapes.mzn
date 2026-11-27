% int_pow with a variable exponent (issue #1006), which is the only way to
% reach the builtin: a constant exponent goes to int_pow_fixed, which the
% standard library turns into products. MiniZinc's semantics: x ^ 0 = 1, also
% for x = 0, and a negative exponent gives 1 div x ^ |y|, truncated, so
% 2 ^ -1 = 0 and (-1) ^ -1 = -1, while 0 ^ -n is undefined and so excluded in
% a root context. Packed: bases and exponents straddling zero, a constant
% negative base, and an exponent that is a view of the base.
var -2..2: x;
var -2..3: y;
var int: p;
var int: q;
var int: r;

constraint p = pow(x, y);
constraint q = pow(-2, y);
constraint r = pow(x, x + 2);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(p) \(q) \(r)"];
