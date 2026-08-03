include "globals.mzn";

% Three optional tasks on a single resource of capacity 2. Heights are chosen so
% that pairs CAN coexist: otherwise MiniZinc's cumulative wrapper short-circuits
% into a disjunctive on the starts and never calls fzn_cumulative_opt (the
% ctest registration also greps the flattened model for the builtin, so a
% rewrite is caught rather than passing vacuously).
%
% Task 3 demands the whole resource for longer than the horizon allows once
% either other task is scheduled, so the interesting solutions are the ones
% where it is absent.
array[1..3] of int: lengths = [2, 2, 3];
array[1..3] of int: heights = [1, 1, 2];
int: capacity = 2;

array[1..3] of var opt 0..3: s;

constraint cumulative(s, lengths, heights, capacity);

output ["ENUMSOL: " ++ show(s)];
