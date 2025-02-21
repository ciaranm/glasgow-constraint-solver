include "globals.mzn";

var 1..5: n;
var 1..5: y;
array[1..5] of var 1..5: x;

constraint (n == count(x, y));
solve satisfy;

output ["ENUMSOL: " ++ show(n) ++ " " ++ show(x) ++ " " ++ show(y)];

