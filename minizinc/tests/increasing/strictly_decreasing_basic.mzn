include "globals.mzn";

array[1..3] of var 1..5: x;
constraint strictly_decreasing(x);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
