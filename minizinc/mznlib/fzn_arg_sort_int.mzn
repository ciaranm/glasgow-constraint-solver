% The stdlib's reified decomposition, for a reified or negated arg_sort. The
% stdlib's own arg_sort.mzn does not include it, since with the stdlib's
% fzn_arg_sort_int a reified call can flatten that body in place. With this one
% it cannot: the body is a builtin, and there is no glasgow_arg_sort_int_reif,
% so without the include `b <-> arg_sort(x, p)` fails to flatten at all.
include "fzn_arg_sort_int_reif.mzn";

predicate glasgow_arg_sort_int(array[int] of var int: x, array[int] of var int: p, int: offset);

% p is indexed 1..length(x) --- arg_sort_int asserts that before it gets here ---
% but its values are indices of x: the stdlib decomposition reads x[p[j]]. So
% ArgSort's offset is the first element of x's index set, min(index_set(x)), and
% it is p's index set that is fixed, not x's. See fzn_symmetric_all_different.mzn
% for why it has to be passed from here rather than assumed to be 1.
%
% With an empty x the min would be undefined, so that case is guarded; p is then
% empty too, and the constraint holds trivially.
predicate fzn_arg_sort_int(array[int] of var int: x, array[int] of var int: p) =
    if length(x) = 0 then true
    else glasgow_arg_sort_int(x, p, min(index_set(x)))
    endif;
