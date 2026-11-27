include "globals.mzn";

array[1..3] of var bool: x;
array[1..3] of var bool: y;
array[1..3] of var bool: a;
array[1..3] of var bool: b;

constraint lex_less(x, y);
constraint lex_lesseq(a, b);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y) ++ " " ++ show(a) ++ " " ++ show(b)];
