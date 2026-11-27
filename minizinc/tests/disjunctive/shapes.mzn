include "globals.mzn";

% The shapes a front end hands disjunctive and disjunctive_strict (#1006),
% each reaching glasgow_disjunctive or glasgow_disjunctive_strict, which the
% lane counts separately. MiniZinc's disjunctive wrapper hands a call to
% disjunctive_strict whenever every duration is known positive, so each
% non-strict call here has a duration that can be zero or below.
var -2..1: p;
var -2..1: q;
array[0..1] of var -1..1: d;
var -1..1: ds;

% Non-strict, with durations that can be negative: the redefinition posts
% d >= 0 itself, as the standard library's decomposition does, and the
% builtin has to see the tightened domains. A task of duration zero may sit at
% time 1, inside the one at the integer-literal start 0, as it could not under
% disjunctive_strict. An index set starting at 0.
constraint disjunctive(array1d(0..2, [p, q, 0]), array1d(0..2, [d[0], d[1], 2]));

% Strict, with two zero-duration tasks on the same start, which may not sit
% strictly inside the length-2 task, over a negative index set.
constraint disjunctive_strict(array1d(-3..-1, [p, q - 1, p]),
    array1d(-3..-1, [0, 2, 0]));

% Single tasks, at an index far from 1. The strict one's duration can be
% negative, and is in no other call, so it is that redefinition's own d >= 0
% that has to tighten it.
constraint disjunctive(array1d(500..500, [q]), array1d(500..500, [d[1]]));
constraint disjunctive_strict(array1d(500..500, [q]), array1d(500..500, [ds]));

% No tasks. The strict form goes through its wrapper; the non-strict wrapper
% takes lb_array of the durations, which is an error on an empty array for
% every solver, so only a direct call reaches that builtin empty.
constraint disjunctive_strict([], []);
constraint fzn_disjunctive([], []);

% A negated call, which has to reach the standard library's decomposition.
constraint not disjunctive_strict([p, d[0]], [2, 1]);

solve satisfy;

output ["ENUMSOL: \(p) \(q) \(d) \(ds)"];
