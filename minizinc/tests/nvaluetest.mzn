include "globals.mzn";

var 1..4: n;
array[1..4] of var 1..3: x;

constraint nvalue(n, x);
constraint n = 2;
constraint x[1] = 1;

solve satisfy;
output ["ENUMSOL: " ++ show(n) ++ " " ++ show(x)];
