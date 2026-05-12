include "globals.mzn";

% Non-strict disjunctive: zero-length tasks float freely.
% Three tasks; with one of length 0 in non-strict mode, the constraint
% reduces to "the two length-2 tasks must not overlap" — the zero-length
% task is unconstrained over the horizon.
array[1..3] of int: lengths = [2, 2, 0];

array[1..3] of var 0..3: s;

constraint disjunctive(s, lengths);

solve satisfy;

output ["ENUMSOL: " ++ show(s)];
