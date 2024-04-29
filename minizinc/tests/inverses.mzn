include "globals.mzn";

array[1..5] of var 1..5: xs;
array[1..5] of var 1..5: ys;
constraint inverse(xs, ys);
constraint (xs[1] <= 3);
constraint (ys[2] <= 2);

solve satisfy;
output ["ENUMSOL: " ++ show(xs) ++ " " ++ show(ys)];
