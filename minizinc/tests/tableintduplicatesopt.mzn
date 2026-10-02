include "globals.mzn";

% As tableintduplicates, but optimising, so the solution lines are soli rather
% than solx (issue #1115).
array[1..3] of var 1..4: x;

constraint table(x, [|
    4, 4, 4 |
    4, 4, 4 |
    2, 1, 4 |
    1, 2, 3 |
    2, 1, 4 |
    1, 2, 3 |]);

solve maximize x[1] + 2 * x[2] - x[3];
output ["OPTSOL: " ++ show(x[1] + 2 * x[2] - x[3])];
