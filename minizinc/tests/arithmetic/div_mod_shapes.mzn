% int_div and int_mod in a root context (issue #1006). MiniZinc's division
% truncates towards zero and its modulus takes the dividend's sign, and a
% divisor of zero makes the constraint false: in a root context the flattener
% says so by punching 0 out of b's domain, which reaches the solver as a domain
% with a hole. Packed here: negative dividends and divisors, a negative
% constant divisor, a constant dividend over a variable divisor, and a variable
% divided by itself, which hands the builtin the same variable twice. Every
% other variable is a function of (a, b), so there are 15 * 6 solutions.
var -7..7: a;
var -3..3: b;
var int: c;
var int: d;
var int: e;
var int: f;
var int: g;
var int: h;
var int: k;
var int: m;

constraint c = a div b;
constraint d = a mod b;
constraint e = a div -2;
constraint f = a mod -3;
constraint g = 5 div b;
constraint h = -5 mod b;
constraint k = b div b;
constraint m = b mod b;

solve satisfy;

output ["ENUMSOL: \(a) \(b) \(c) \(d) \(e) \(f) \(g) \(h) \(k) \(m)"];
