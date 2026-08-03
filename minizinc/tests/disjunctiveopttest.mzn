include "globals.mzn";

% Optional-task disjunctive, routed through glasgow_cumulative_opt with unit
% demands and capacity 1. A zero-duration task is in the array on purpose: it is
% what stops disjunctive_opt short-circuiting into disjunctive_strict_opt (which
% it does whenever every duration is known positive), so this is the path the
% redefinition actually covers --- and the non-strict semantics, under which a
% zero-duration task may sit anywhere, including inside another task.
array[1..3] of int: durations = [2, 2, 0];

array[1..3] of var opt 0..3: s;

constraint disjunctive(s, durations);

output ["ENUMSOL: " ++ show(s)];
