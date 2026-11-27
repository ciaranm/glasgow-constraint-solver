include "globals.mzn";

array[1..4] of var 1..3: x;

constraint count_geq(x, 2, 1);
constraint count_leq(x, 1, 2);
constraint count_neq(x, 3, 0);
constraint at_least(1, x, 2);
constraint at_most(2, x, 1);
constraint exactly(1, x, 3);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
