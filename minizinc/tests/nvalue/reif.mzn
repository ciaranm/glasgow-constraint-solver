include "globals.mzn";

% nvalue in a reified, half-reified and negated context, which reach the
% stdlib's fzn_nvalue_reif decomposition and have to flatten for us and agree.
% The function form is total, so it reaches glasgow_nvalue at the root even
% under a reification, and is the one call here that does.
array[1..3] of var 0..1: x;
var 0..3: n;
array[1..3] of var bool: b;

constraint b[1] <-> nvalue(n, x);
constraint b[2] -> nvalue(1, [x[1], x[2]]);
constraint not nvalue(2, [x[2], x[3]]);
constraint b[3] <-> nvalue(x) = 2;

solve satisfy;

output ["ENUMSOL: \(x) \(n) \(b)"];
