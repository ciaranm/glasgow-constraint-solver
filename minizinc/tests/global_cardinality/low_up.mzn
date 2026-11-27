include "globals.mzn";

% Low/up (bounds) form: each cover value must occur between 1 and 2 times.
array[1..4] of var 1..3: x;

constraint global_cardinality_low_up(x, [1, 2, 3], [1, 1, 1], [2, 2, 2]);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
