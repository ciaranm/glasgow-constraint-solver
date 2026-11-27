include "globals.mzn";

% lex_greater rewrites to lex_less(b, a) in the stdlib, so this also
% exercises the unequal-length lex_less path with arguments swapped.
array[1..2] of var 1..2: a;
array[1..3] of var 1..2: b;

constraint lex_greater(a, b);

solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b)];
