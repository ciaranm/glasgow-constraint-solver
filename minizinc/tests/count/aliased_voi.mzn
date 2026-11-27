include "globals.mzn";

% The value of interest is in the array, and how_many is not (issue #1201).
var 3..7: a;
var 1..5: b;
var 0..4: c;

constraint count([b, b, 2, c, c], b) = a;

solve satisfy;
output ["ENUMSOL: " ++ show([a, b, c])];
