include "globals.mzn";

% A negated empty decreasing that MiniZinc cannot settle while flattening, so the
% solver runs: an empty array is decreasing and strictly decreasing, so b and c
% must be false and x must be 1 (#1146).
array[1..0] of var 1..3: e;
var 1..2: x;
var bool: b;
var bool: c;
constraint b -> not decreasing(e);
constraint c -> not strictly_decreasing(e);
constraint b \/ c \/ x = 1;

solve satisfy;

output ["ENUMSOL: \(x) \(b) \(c)"];
