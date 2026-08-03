predicate glasgow_cumulative_opt(array[int] of var int: s,
    array[int] of var int: d, array[int] of var int: r,
    array[int] of var bool: o, var int: b);

% An optional start is a presence Boolean and an underlying integer, which
% occurs/deopt split apart. deopt is undefined on a value fixed absent, so
% guard it the way the Gecode and OR-Tools libraries do: a definitely-absent
% task gets any start at all, since nothing constrains it.
predicate fzn_cumulative_opt(array[int] of var opt int: s,
    array[int] of var int: d, array[int] of var int: r,
    var int: b) =
    glasgow_cumulative_opt(
        [ if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in s ],
        d, r, [ occurs(si) | si in s ], b);
