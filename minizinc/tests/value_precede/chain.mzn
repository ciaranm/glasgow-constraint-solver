include "globals.mzn";

% value_precede_chain([1, 2, 3], x): 1 precedes 2, and 2 precedes 3.
% Equivalently, the first occurrence of 1, 2, and 3 (if any) appear in
% chain order.
array[1..4] of var 1..3: x;
constraint value_precede_chain([1, 2, 3], x);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
