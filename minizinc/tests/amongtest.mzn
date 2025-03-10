include "globals.mzn";

var 1..5: n;
array[1..5] of var 1..5: x;

constraint (n == among(x, {2, 3, 4}));
solve satisfy;

output ["ENUMSOL: " ++ show(n) ++ " " ++ show(x)];

