predicate glasgow_disjunctive_strict_opt(array[int] of var int: s,
    array[int] of var int: d, array[int] of var bool: o);

% Strict optional disjunctive: as fzn_disjunctive_opt, but a present
% zero-duration task may not sit strictly inside a present task's active
% interval either.
%
% This predicate has no redefinition in most solvers' libraries, and could not
% have one here before #735. A task consuming nothing for no time is invisible
% to a resource profile, so no route through cumulative can express it; the
% pairwise separation clause can, and does, with an all-fixed check whose proof
% is a bare RUP against that clause. Zero durations are the only case where it
% differs from fzn_disjunctive_opt at all.
predicate fzn_disjunctive_strict_opt(array[int] of var opt int: s,
    array[int] of var int: d) =
    forall(i in index_set(d)) (d[i] >= 0)
    /\ glasgow_disjunctive_strict_opt(
        [ if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in s ],
        d, [ occurs(si) | si in s ]);
