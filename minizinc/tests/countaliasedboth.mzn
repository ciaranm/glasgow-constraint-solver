include "globals.mzn";

% The value of interest and how_many are both in the array, so a push to
% either moves a position too (issue #1201).
var 3..5: a;
var 3..7: b;
var 2..5: c;

constraint count([c, a, 1, a, b], c) = b;

solve satisfy;
output ["ENUMSOL: " ++ show([a, b, c])];
