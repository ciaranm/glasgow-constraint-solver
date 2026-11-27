include "globals.mzn";

% Every form of count in a reified, half-reified or negated context. None of
% them reaches our redefinitions directly: MiniZinc takes the stdlib's _reif
% decompositions, which have to flatten for us and agree. Those decompositions
% count through the function form, which is total, so it is posted at the root
% as glasgow_count_eq, and the flattener merges every call over the same array
% and value into one: three in all, for (x, y), (x, 0) and (x, 1).
array[1..2] of var 0..1: x;
var 0..1: y;
var 0..2: c;
array[1..9] of var bool: b;

constraint b[1] <-> count_eq(x, y, c);
constraint b[2] -> count_geq(x, y, c);
constraint not count_gt(x, y, c);
constraint b[3] <-> count_leq(x, y, c);
constraint b[4] -> count_lt(x, y, c);
constraint b[5] <-> count_neq(x, y, c);
constraint b[6] <-> at_least(1, x, 0);
constraint b[7] -> at_most(1, x, 1);
constraint not exactly(2, x, 1);
constraint b[8] <-> count(x, 1) = 1;
constraint b[9] <-> count(x, 1, c);

solve satisfy;

output ["ENUMSOL: \(x) \(y) \(c) \(b)"];
