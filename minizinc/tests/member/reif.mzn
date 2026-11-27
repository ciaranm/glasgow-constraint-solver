include "globals.mzn";

% member over integers and over bools in a reified, half-reified and negated
% context, which reach the stdlib's fzn_member_int_reif and
% fzn_member_bool_reif decompositions and have to flatten for us and agree.
% None of them reaches a builtin.
array[1..2] of var 0..2: x;
var 0..2: y;
var bool: p;
var bool: q;
array[1..4] of var bool: b;

constraint b[1] <-> member(x, y);
constraint b[2] -> member(x, 1);
constraint not member([x[1], 2], y);
constraint b[3] <-> member([p, q], true);
constraint not member([p, true], false);
constraint b[4] -> member([q], p);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(p) \(q) \(b)"];
