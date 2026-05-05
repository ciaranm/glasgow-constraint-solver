include "globals.mzn";

array[1..3] of var 1..3: x;
constraint symmetric_all_different(x);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
