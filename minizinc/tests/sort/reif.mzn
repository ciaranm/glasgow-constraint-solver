include "globals.mzn";

% Reified, half-reified and negated sort. The stdlib's fzn_sort_reif is
% `b <-> sort(x) = y`, and its function form posts sort at the root, so each of
% these reaches the builtin too, and the count insists on all three. The
% arrays share an index set that does not start at 1: the stdlib's
% decomposition compares sort(x), indexed like x, with y, so arrays with
% different index sets fail to flatten in a reified context for every solver.
array[0..1] of var 0..1: x;
array[0..1] of var 0..1: y;
array[0..1] of var 0..1: u;
var bool: r;
var bool: s;
constraint r <-> sort(x, y);
constraint s -> sort(y, x);
constraint not sort(u, x);

solve satisfy;
output ["ENUMSOL: \(x) \(y) \(u) \(r) \(s)"];
