include "globals.mzn";

array[1..3] of var 1..4: x;

constraint table(x, [|
    1, 2, 3 |
    1, 3, 2 |
    2, 1, 4 |
    4, 4, 4 |]);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
