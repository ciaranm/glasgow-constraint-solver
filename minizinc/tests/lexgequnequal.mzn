include "globals.mzn";

% lex_greatereq rewrites to lex_lesseq(b, a) in the stdlib.
array[1..3] of var 1..2: a;
array[1..2] of var 1..2: b;

constraint lex_greatereq(a, b);

solve satisfy;
output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b)];
