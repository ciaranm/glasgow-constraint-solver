predicate glasgow_disjunctive_opt(array[int] of var int: s,
    array[int] of var int: d, array[int] of var bool: o);

% An optional start is a presence Boolean and an underlying integer, which
% occurs/deopt split apart. deopt is undefined on a value fixed absent, so
% guard it the way the Gecode and OR-Tools libraries do: a definitely-absent
% task gets any start at all, since nothing constrains it.
%
% This used to route to fzn_cumulative_opt at unit demands and capacity 1,
% which was correct but gave an optional disjunctive the time-indexed
% O(n x horizon) encoding that issue #495 removed from the non-optional form,
% and cost it detectable precedences. Disjunctive takes presences natively now
% (#735), so the pairwise O(n^2) encoding applies here too.
predicate fzn_disjunctive_opt(array[int] of var opt int: s,
    array[int] of var int: d) =
    forall(i in index_set(d)) (d[i] >= 0)
    /\ glasgow_disjunctive_opt(
        [ if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in s ],
        d, [ occurs(si) | si in s ]);
