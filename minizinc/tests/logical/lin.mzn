% bool_lin_eq and bool_lin_le with negative and zero coefficients, a variable
% right-hand side, constants and repeated variables among the terms, and the
% two-term unit-coefficient forms that fzn-glasgow rewrites into a comparison
% of two variables (#1006). MiniZinc itself writes a Boolean sum as bool2int
% and int_lin_eq, so these are direct calls to the builtins.
array[1..4] of var bool: b;
var -3..3: c;
constraint bool_lin_eq([2, -1, 0, 3], b, c);
constraint bool_lin_le([2, -1, 0, -3], b, 0);

var bool: d1; var bool: d2; var bool: d3;
constraint bool_lin_le([1, 2, 1, -1], [true, d1, d2, d1], 2);
constraint bool_lin_eq([-2, 1, 1], [d3, d3, d2], 0);

% e1 + e2 = 1, e1 + e3 >= 1 written as -e1 - e3 <= -1, and f = -e3.
var bool: e1; var bool: e2; var bool: e3; var -1..1: f;
constraint bool_lin_eq([1, 1], [e1, e2], 1);
constraint bool_lin_le([-1, -1], [e1, e3], -1);
constraint bool_lin_eq([-1], [e3], f);

solve satisfy;
output ["ENUMSOL: \(b) \(c) \([d1, d2, d3]) \([e1, e2, e3]) \(f)"];
