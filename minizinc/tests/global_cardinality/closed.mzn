include "globals.mzn";

% Closed form: every variable must take a cover value, so value 4 is forbidden
% even though it is in the variable domains.
array[1..3] of var 1..4: x;
array[1..3] of var 0..3: c;

constraint global_cardinality_closed(x, [1, 2, 3], c);
constraint c[1] = 1;

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(c)];
