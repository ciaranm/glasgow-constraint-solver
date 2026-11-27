include "globals.mzn";

% all_different, alldifferent_except and alldifferent_except_0 in reified,
% half-reified and negated contexts, which reach the stdlib's _reif
% decompositions and have to flatten for us and agree; two of them are over
% bools. None of them reaches a builtin. bool.mzn has bools at the root.
array[1..3] of var 0..2: x;
var bool: p;
var bool: q;
array[1..5] of var bool: b;

constraint b[1] <-> all_different(x);
constraint b[2] -> all_different([x[1], x[2]]);
constraint not all_different([x[2], x[3], 0]);
constraint b[3] <-> alldifferent_except(x, {1});
constraint b[4] -> alldifferent_except_0([x[1], x[3]]);
constraint not alldifferent_except([p, q, true], {0});
constraint b[5] <-> all_different([p, q]);

solve satisfy;

output ["ENUMSOL: \(x) \(p) \(q) \(b)"];
