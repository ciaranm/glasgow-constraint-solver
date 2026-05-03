include "globals.mzn";

% Longer side on the left, exercising standard lex semantics:
% [1,1,1] >_lex [1,1] so lex_lesseq fails; whereas if the common prefix
% has any variation, that determines the order.
array[1..3] of var 1..2: x;
array[1..2] of var 1..2: y;

constraint lex_lesseq(x, y);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y)];
