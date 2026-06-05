predicate glasgow_global_cardinality(array[int] of var int: x, array[int] of int: cover, array[int] of var int: counts);
predicate glasgow_global_cardinality_closed(array[int] of var int: x, array[int] of int: cover, array[int] of var int: counts);

predicate fzn_global_cardinality(
  array [int] of var int: x,
  array [int] of int: cover,
  array [int] of var int: counts,
) = glasgow_global_cardinality(x, cover, counts);
