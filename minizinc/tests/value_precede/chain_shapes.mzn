include "globals.mzn";

% The shapes a front end can misread for value_precede_chain (#1006), each of
% which reaches the builtin: a chain indexed from 0 with negative values and one
% outside every domain, which forbids the value after it; an empty chain; a
% chain that repeats a value, which then precedes itself and so cannot occur,
% and nor can anything after it; an x indexed from -1 with integer literals and
% a repeated variable; and an enum chain over an enum-valued x. An empty x is
% left out: the stdlib's decomposition takes ub_array(x), so MiniZinc's default
% solver cannot run it.
array[1..3] of var -2..0: xa;
constraint value_precede_chain(array1d(0..3, [0, -2, 7, -1]), xa);
constraint xa[2] = xa[3];

array[1..2] of var 1..2: xb;
array[int] of int: none = [];
constraint value_precede_chain(none, xb);
constraint xb[1] = xb[2];

array[1..3] of var 1..4: xr;
constraint value_precede_chain([3, 1, 1, 2], xr);
constraint xr[1] = 3 /\ xr[2] = xr[3];

var 1..3: a;
var 1..3: b;
constraint value_precede_chain([3, 1, 2], array1d(-1..2, [a, 3, b, a]));

enum Col = {R, G, B};
array[1..3] of var Col: xe;
constraint value_precede_chain([B, R], xe);
constraint xe[1] != G;

solve satisfy;
output ["ENUMSOL: \(xa) \(xb) \(xr) \(a) \(b) \(xe)"];
