include "fzn_cumulative_opt.mzn";

% Optional-task disjunctive is optional-task cumulative with unit demands and
% capacity 1: at most one present task can occupy any time point. Zero-duration
% tasks are never active under either reading, which is exactly the non-strict
% semantics this predicate carries (disjunctive_opt routes to
% disjunctive_strict_opt whenever every duration is known positive, so the
% zero-duration case is the one that reaches here).
%
% There is deliberately no fzn_disjunctive_strict_opt redefinition: strict
% disjunctive additionally forbids a zero-duration task from sitting inside
% another task, and a task that consumes no resource for no time is invisible to
% Cumulative. That one keeps the library decomposition.
predicate fzn_disjunctive_opt(array[int] of var opt int: s,
    array[int] of var int: d) =
    forall(i in index_set(d)) (d[i] >= 0)
    /\ fzn_cumulative_opt(s, d, [1 | i in index_set(d)], 1);
