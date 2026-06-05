include "fzn_global_cardinality.mzn";

% The low/up (bounds) form is expressed by giving each cover value a fresh
% count variable whose domain is the requested lbound..ubound range, then
% reusing the counts form.
predicate fzn_global_cardinality_low_up(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of int: lbound,
  array [int] of int: ubound,
) =
  let {
    array [index_set(cover)] of var 0..length(x): counts;
    constraint forall (i in index_set(cover)) (lbound[i] <= counts[i] /\ counts[i] <= ubound[i]);
  } in glasgow_global_cardinality(x, cover, counts);
