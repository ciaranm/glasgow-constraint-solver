include "fzn_global_cardinality.mzn";

% As fzn_global_cardinality_low_up, but closed: every variable must take a
% cover value.
predicate fzn_global_cardinality_low_up_closed(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of int: lbound,
  array [int] of int: ubound,
) =
  let {
    array [index_set(cover)] of var 0..length(x): counts;
    constraint forall (i in index_set(cover)) (lbound[i] <= counts[i] /\ counts[i] <= ubound[i]);
  } in glasgow_global_cardinality_closed(x, cover, counts);
