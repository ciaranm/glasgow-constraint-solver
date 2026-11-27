include "globals.mzn";

% among in a reified, half-reified and negated context, which reach the
% stdlib's fzn_among_reif decomposition and have to flatten for us and agree,
% and among as a function, which is total and so reaches glasgow_among at the
% root even under a reification: once for x over S, shared by the two calls
% that use it, once for x over the empty set, and once for an array that
% shares a variable with x and holds a literal in S.
set of int: S = {-1, 2};
array[1..2] of var -1..2: x;
var 0..2: n;
array[1..4] of var bool: b;

constraint b[1] <-> among(n, x, S);
constraint b[2] -> among(1, x, S);
constraint not among(2, x, {0, 2});
constraint b[3] <-> among(x, S) = 1;
constraint b[4] <-> among(x, {}) = 0;
constraint among(x, S) + among([x[1], 2], S) = 2;

solve satisfy;

output ["ENUMSOL: \(x) \(n) \(b)"];
