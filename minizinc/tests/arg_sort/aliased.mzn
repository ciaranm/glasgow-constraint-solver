include "globals.mzn";

% The same variable twice in p, which can then be no permutation, so there is
% no solution; the pattern checks that p reached the builtin with the repeat.
array[0..1] of var 0..2: x;
var 0..1: q;
constraint arg_sort(x, [q, q]);

solve satisfy;
output ["ENUMSOL: \(x) \(q)"];
