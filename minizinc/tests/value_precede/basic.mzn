include "globals.mzn";

% value_precede(1, 2, x): every occurrence of 2 in x must have an
% earlier occurrence of 1.
array[1..3] of var 1..3: x;
constraint value_precede(1, 2, x);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
