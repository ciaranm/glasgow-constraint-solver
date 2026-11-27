include "globals.mzn";

% The same array on both sides of lex_less, which no assignment satisfies; the
% builtin gets the same variables twice.
array[0..2] of var 0..1: x;
constraint lex_less(x, x);

solve satisfy;
output ["ENUMSOL: \(x)"];
