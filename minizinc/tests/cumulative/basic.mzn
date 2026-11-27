include "globals.mzn";

% Three tasks on a single resource of capacity 2.
% Task i runs for lengths[i] time units, demands heights[i] of the resource.
% Heights chosen so that pairs CAN coexist — otherwise MiniZinc's cumulative
% wrapper short-circuits into a disjunctive on the starts and never calls
% fzn_cumulative.
array[1..3] of int: lengths = [2, 2, 1];
array[1..3] of int: heights = [1, 1, 1];
int: capacity = 2;

array[1..3] of var 0..5: s;

constraint cumulative(s, lengths, heights, capacity);

% Constrain the makespan so the search space is small but non-trivial.
var 0..6: makespan;
constraint forall(i in 1..3) (makespan >= s[i] + lengths[i]);

solve minimize makespan;

output ["OPTSOL: " ++ show(makespan)];
