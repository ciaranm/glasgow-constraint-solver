include "globals.mzn";

array[1..3] of var 1..4: x;
var 1..5: y;

constraint member(x, y);

solve satisfy;

output ["ENUMSOL: " ++ show(y) ++ " " ++ show(x)];
