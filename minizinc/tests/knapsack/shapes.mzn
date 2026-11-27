include "globals.mzn";

% The shapes a front end hands knapsack (#1006), each reaching
% glasgow_knapsack, which the lane counts. The wrapper insists on one index
% set for weights, profits and counts, so it is the index sets themselves
% and the array contents that vary. Weights and profits differ everywhere, so
% swapping them, or the two totals, changes the answers. Every count and
% total starts at 0, which Knapsack needs (#1337).

% An index set starting at -1, a zero weight and a zero profit, and counts
% above 1.
array[-1..1] of var 0..2: x;
var 0..4: W;
var 0..5: P;
constraint knapsack(array1d(-1..1, [0, 2, 1]), array1d(-1..1, [1, 0, 2]), x, W, P);

% Enum-indexed, with an integer-literal count and a variable repeated.
enum Item = {Apple, Pear, Plum};
var 0..6: W2;
var 0..9: P2;
constraint knapsack([Apple: 2, Pear: 1, Plum: 3], [Apple: 1, Pear: 3, Plum: 2],
    [Apple: x[0], Pear: 1, Plum: x[0]], W2, P2);

% A single item with a zero profit, a literal total, at an index far from 1.
var 0..2: W3;
constraint knapsack(array1d(99..99, [2]), array1d(99..99, [0]),
    array1d(99..99, [x[1]]), W3, 0);

% No items. The wrapper takes lb_array of the weights, which is an error on
% an empty array for every solver, so only a direct call reaches the builtin.
var 0..1: W4;
var 0..1: P4;
constraint fzn_knapsack([], [], [], W4, P4);

% A reified call, which has to reach the standard library's decomposition.
var bool: rb;
constraint rb <-> knapsack([1, 2], [1, 2], [x[-1], x[1]], 2, 2);

solve satisfy;

output ["ENUMSOL: \(x) \(W) \(P) \(W2) \(P2) \(W3) \(W4) \(P4) \(rb)"];
