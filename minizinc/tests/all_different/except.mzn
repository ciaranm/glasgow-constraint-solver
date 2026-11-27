include "globals.mzn";

array[1..3] of var 0..3: x;
constraint all_different_except(x, {0, 1});

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
