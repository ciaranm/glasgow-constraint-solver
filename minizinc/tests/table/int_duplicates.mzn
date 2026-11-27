include "globals.mzn";

% Duplicate rows: MiniZinc keeps them, and every solution here is matched by
% two rows, which made the proof's solution lines fail (issue #1115).
array[1..3] of var 1..4: x;

constraint table(x, [|
    1, 2, 3 |
    1, 2, 3 |
    2, 1, 4 |
    4, 4, 4 |
    2, 1, 4 |
    4, 4, 4 |]);

solve satisfy;
output ["ENUMSOL: " ++ show(x)];
