include "globals.mzn";

% Strict optional disjunctive: the case that had no redefinition before #735 and
% could not have had one built on cumulative, because a task consuming nothing
% for no time is invisible to a resource profile. Task 3 has duration zero, and
% under the strict reading a *present* zero-duration task may not sit inside a
% present task's active interval --- which is the only thing separating this
% model's solution set from disjunctiveopttest's.
array[1..3] of int: durations = [2, 2, 0];

array[1..3] of var opt 0..3: s;

constraint disjunctive_strict(s, durations);

output ["ENUMSOL: " ++ show(s)];
