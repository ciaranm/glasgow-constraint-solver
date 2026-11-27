include "globals.mzn";

% how_many is also every position: the whole constraint flattens to one
% glasgow_among with y in both places. y's definition range is wider than 100
% values, so the lower bound's at-least-one is a cover keyed on the values y can
% still take, and the justification used to read them after its own push
% (issue #1308).
var {-98, 1, 2, 3}: y;

constraint among(y, [y, y, y], {1, 2, 3});

solve satisfy;
output ["ENUMSOL: " ++ show(y)];
