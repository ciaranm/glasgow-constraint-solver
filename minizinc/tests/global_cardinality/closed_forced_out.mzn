include "globals.mzn";

% An integer literal outside the cover of a closed global_cardinality, which
% leaves no solution: the closed restriction has to reach the builtin with the
% constant in its scope.
var 1..3: a;
array[1..2] of var 0..3: c;
constraint global_cardinality_closed([a, 3], [1, 2], c);

solve satisfy;
output ["ENUMSOL: \(a) \(c)"];
