include "globals.mzn";

% The shapes a front end hands the optional-task cumulative (#1006), each
% reaching glasgow_cumulative_opt, which the lane counts. The redefinition
% splits every start into occurs/deopt, with a guard for a start that is
% fixed absent, so the array holds the literal <>, which has to arrive as a
% constant-false presence, and an integer literal, a constant-true one.
var opt -1..1: a;
var opt -1..1: b;
var 0..1: d;
var 1..2: c;

% Literal absent and present starts beside optional variables with negative
% values, over an index set starting at 0. The absent task could not fit
% beside anything, so it is only absent that keeps the model satisfiable.
constraint cumulative(array1d(0..3, [a, <>, 0, b]), array1d(0..3, [2, 3, 1, 1]),
    array1d(0..3, [1, 2, 1, 1]), 2);

% A duration that can be zero and a height that is zero, a variable capacity,
% a repeated start, and a negative index set. The variable duration also
% sends native Gecode to the standard decomposition.
constraint cumulative(array1d(-2..0, [a, b, a]), array1d(-2..0, [d, 1, 2]),
    array1d(-2..0, [2, 1, 0]), c);

% A single optional task, which only fits when the capacity is 2.
constraint cumulative(array1d(9..9, [b]), array1d(9..9, [2]),
    array1d(9..9, [2]), c);

% A half-reified call, which has to reach the standard library's
% decomposition.
var bool: hb;
constraint hb -> cumulative([a, b], [2, 1], [1, 1], 1);

solve satisfy;

output ["ENUMSOL: \(a) \(b) \(d) \(c) \(hb)"];
