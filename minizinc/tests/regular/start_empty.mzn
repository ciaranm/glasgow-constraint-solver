include "regular.mzn";

% No variables and a start state other than 1 that is final (#1328), so the
% empty sequence is accepted; state 1 is not final, which is what the start
% state used to be read as.
array[1..0] of var 1..2: x;
var 1..2: y;
array[1..2, 1..2] of int: d = [| 2, 1 | 1, 2 |];
constraint regular(x, 2, 2, d, 2, {2});

solve satisfy;
output ["ENUMSOL: " ++ show(y)];
