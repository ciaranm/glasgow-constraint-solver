include "regular.mzn";

% An empty set of final states, so nothing is accepted (#1006). The final
% states arrive as an empty set, which fzn-glasgow must read as "no state is
% final" rather than as anything else.
array[1..2] of var 1..2: x;
constraint regular(x, 2, 2, [| 2, 1 | 1, 2 |], 1, {});

solve satisfy;
output ["ENUMSOL: \(x)"];
