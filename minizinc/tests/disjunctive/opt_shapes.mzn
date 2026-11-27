include "globals.mzn";

% The shapes a front end hands the optional-task disjunctives (#1006), each
% reaching glasgow_disjunctive_opt or glasgow_disjunctive_strict_opt, which
% the lane counts separately. The redefinitions split every start into
% occurs/deopt, with a guard for a start that is fixed absent, so the arrays
% hold the literal <>, which has to arrive as a constant-false presence, and
% integer literals, constant-true ones. The non-strict call has a zero
% duration, without which its wrapper hands it to the strict form.
var opt -1..1: a;
var opt -1..1: b;
var opt -1..1: e;
var -1..1: d;

% Non-strict: literal absent and present starts beside optional variables
% with negative values, a zero duration, over an index set starting at 0.
constraint disjunctive(array1d(0..3, [a, <>, 0, b]), array1d(0..3, [2, 3, 0, 1]));

% Strict: a zero-duration task that may not sit inside a present one, a
% variable duration that can be negative, which the strict redefinition's own
% d >= 0 has to tighten (the non-strict wrapper posts one of its own), a
% repeated start and a literal absent one, over a negative index set. The
% variable duration also sends native Gecode to the standard decomposition.
constraint disjunctive_strict(array1d(-3..0, [e, <>, b, e]),
    array1d(-3..0, [2, 1, 0, d]));

% A single optional task.
constraint disjunctive_strict(array1d(7..7, [a]), array1d(7..7, [1]));

% A reified call, which has to reach the standard library's decomposition.
var bool: rb;
constraint rb <-> disjunctive([a, e], [2, d]);

solve satisfy;

output ["ENUMSOL: \(a) \(b) \(e) \(d) \(rb)"];
