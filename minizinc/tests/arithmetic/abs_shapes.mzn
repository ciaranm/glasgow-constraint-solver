% int_abs shapes (issue #1006): a domain straddling zero, a domain with holes
% on both sides of it, a domain wholly negative, a variable equal to its own
% absolute value, which hands the builtin the same variable twice, and the
% absolute value of a difference.
var -3..2: x;
var {-3, -1, 0, 2, 5}: y;
var int: a;
var int: b;
var -2..-1: n;
var int: c;
var -2..2: w;

constraint a = abs(x);
constraint b = abs(y);
constraint c = abs(n);
constraint abs(w) = w;
constraint abs(x - y) <= 3;

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(a) \(b) \(n) \(c) \(w)"];
