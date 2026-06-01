include "globals.mzn";

array[1..3] of var 0..2: x;
array[1..3] of var 0..2: y;
constraint sort(x, y);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y)];
