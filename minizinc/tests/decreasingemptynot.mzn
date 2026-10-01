include "globals.mzn";

% An empty array is decreasing, so its negation has no solution (#1146).
array[1..0] of var 1..3: e;
var 1..2: x;
constraint not decreasing(e);

solve satisfy;

output ["ENUMSOL: \(x)"];
