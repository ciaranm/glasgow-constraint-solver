include "globals.mzn";

array[1..3] of var 1..3: x;

constraint all_equal(x);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
