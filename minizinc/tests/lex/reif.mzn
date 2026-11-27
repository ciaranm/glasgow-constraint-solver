include "globals.mzn";

array[1..3] of var 1..2: x;
array[1..3] of var 1..2: y;
var bool: c1;
var bool: c2;

constraint c1 <-> lex_less(x, y);
constraint c2 <-> lex_lesseq(x, y);

solve satisfy;
output ["ENUMSOL: " ++ show(x) ++ " " ++ show(y) ++ " " ++ show(c1) ++ " " ++ show(c2)];
