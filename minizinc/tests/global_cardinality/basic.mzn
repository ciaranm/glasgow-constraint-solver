include "globals.mzn";

% Open counts form: value 4 is outside the cover, so it is not counted.
array[1..3] of var 1..4: x;
array[1..3] of var 0..3: c;

constraint global_cardinality(x, [1, 2, 3], c);
constraint c = [1, 1, 0];

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(c)];
