include "globals.mzn";

array[1..3] of var bool: x;

constraint table(x, [|
    true,  false, true  |
    false, true,  true  |
    true,  true,  false |]);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
