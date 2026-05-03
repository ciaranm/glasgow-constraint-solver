include "globals.mzn";

array[1..3] of var 1..2: x;
array[1..3] of var 1..2: y;
array[1..3] of var 1..2: a;
array[1..3] of var 1..2: b;

constraint lex_lesseq(x, y);
constraint lex_greatereq(a, b);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y) ++ " " ++ show(a) ++ " " ++ show(b)];
