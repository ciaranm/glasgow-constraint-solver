include "globals.mzn";

% how_many is the value of interest: the whole constraint is count(x, y) = y,
% which flattens to one glasgow_count_eq with y in both places (issue #1201).
var 3..4: y;
var 1..3: a;
var 1..2: b;
var 1..2: c;
var 1..2: d;

constraint count([a, b, c, d], y) = y;

solve satisfy;
output ["ENUMSOL: " ++ show([y, a, b, c, d])];
