include "globals.mzn";

array[1..3] of var 0..2: x;
array[1..3] of var 1..3: p;
constraint arg_sort(x, p);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(p)];
