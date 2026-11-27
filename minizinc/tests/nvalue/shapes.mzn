include "globals.mzn";

% The shapes a front end hands nvalue (#1006): an empty array, which the stdlib
% wrapper answers with n = 0 before any builtin is posted; a single element
% indexed from 3 with negative values; integer literals among the variables,
% one of them repeated and one negative; a constant count over a bool array in
% which one variable appears twice beside a literal, which MiniZinc coerces to
% integers; the count as one of the array's own variables; and the function
% form over a two-dimensional array indexed from negative values.
array[1..0] of var 1..3: e;
var 0..1: ne;
array[3..3] of var -2..-1: s;
var 0..2: ns;
var -1..0: a;
var {2, 3}: b;
var 1..5: n;
var bool: p;
var bool: q;
var 1..3: k;
var 1..3: kp;
var 1..3: kq;
array[-2..-1, 0..1] of var {-5, 4}: g;

constraint nvalue(ne, e);
constraint nvalue(ns, s);
constraint nvalue(n, [a, 2, b, 2, -1]);
constraint nvalue(2, [p, p, q, true]);
constraint nvalue(k, [k, kp, kq]);
constraint nvalue(g) = 1;

solve satisfy;

output ["ENUMSOL: \(ne) \(s) \(ns) \(a) \(b) \(n) \(p) \(q) \(k) \(kp) \(kq) \(g)"];
