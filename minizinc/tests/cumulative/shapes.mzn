include "globals.mzn";

% The shapes a front end hands cumulative (#1006), each reaching
% glasgow_cumulative, which the lane counts. MiniZinc's wrapper rewrites a
% cumulative into a disjunctive (or drops it) when every height is fixed and no
% two tasks fit together, and drops a single task with a fixed height, so
% every call here has either a variable height or two heights that fit under
% the capacity. The calls share variables to keep the solution count small.
var -1..0: p;
var -1..0: q;
var 0..1: hp;
var 0..1: hq;
var 0..1: c;
var 0..2: u;
var 0..1: dz;

% A zero capacity, which only tasks of zero height or zero duration can meet:
% one task of each, over an index set starting at 0 and a repeated start.
constraint cumulative(array1d(0..2, [p, q, p]), array1d(0..2, [2, 0, 1]),
    array1d(0..2, [0, 1, 0]), 0);

% Negative starts over a negative index set, with variable heights and a
% variable capacity.
constraint cumulative(array1d(-3..-2, [p, q]), array1d(-3..-2, [1, 2]),
    array1d(-3..-2, [hp, hq]), c);

% A single task, which the wrapper keeps only because its height is a
% variable, at an index far from 1.
constraint cumulative(array1d(1000..1000, [q]), array1d(1000..1000, [1]),
    array1d(1000..1000, [hq]), c);

% A start variable repeated, beside an integer literal it has to avoid.
constraint cumulative([u, 1, u], [1, 1, 1], [1, 1, 1], 2);

% A duration that can be zero, and a capacity that is an expression.
constraint cumulative([u, p + 1], [dz, 2], [2, 1], c + 2);

% No tasks at all. The wrapper drops an empty cumulative before any solver
% sees it, so only a direct call reaches the builtin with empty arrays.
constraint fzn_cumulative([], [], [], c);

% A reified call, which has to reach the standard library's decomposition.
var bool: rb;
constraint rb <-> cumulative([u, q + 2], [1, 1], [2, 1], c + 2);

solve satisfy;

output ["ENUMSOL: \(p) \(q) \(hp) \(hq) \(c) \(u) \(dz) \(rb)"];
