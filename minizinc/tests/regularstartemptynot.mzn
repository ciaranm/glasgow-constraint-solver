include "regular.mzn";

% No variables and a start state other than 1 that is not final (#1328), so
% the empty sequence is rejected; state 1 is final, which is what the start
% state used to be read as.
array[1..0] of var 1..2: x;
var 1..2: y;
array[1..2, 1..2] of int: d = [| 2, 1 | 1, 2 |];
constraint regular(x, 2, 2, d, 2, {1});

solve satisfy;
output ["ENUMSOL: " ++ show(y)];
