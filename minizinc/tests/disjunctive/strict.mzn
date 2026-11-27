include "globals.mzn";

% Strict disjunctive: zero-length tasks must not sit strictly inside any
% other task's open active interval.
% With one task of length 0 in strict mode, the constraint forbids the
% zero-length task at times 1 and 2 (inside either length-2 task that
% starts at 0 or 1), so search has fewer feasible layouts than the
% non-strict counterpart.
array[1..3] of int: lengths = [2, 2, 0];

array[1..3] of var 0..3: s;

constraint disjunctive_strict(s, lengths);

solve satisfy;

output ["ENUMSOL: " ++ show(s)];
