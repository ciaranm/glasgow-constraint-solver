include "globals.mzn";

% seq_precede_chain: i precedes i+1 for all positive i. So x[0] must be
% ≤ 1, and the running max of x can grow by at most 1 per step.
array[1..4] of var 1..4: x;
constraint seq_precede_chain(x);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
