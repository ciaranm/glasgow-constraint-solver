include "globals.mzn";

% Standard lex semantics: longer wins on equal common prefix, so
% [1,1] <_lex [1,1,1].
array[1..2] of var 1..2: x;
array[1..3] of var 1..2: y;

constraint lex_less(x, y);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y)];
