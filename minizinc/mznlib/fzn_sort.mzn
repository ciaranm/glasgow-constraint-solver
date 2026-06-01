predicate glasgow_sort(array[int] of var int: x, array[int] of var int: y);

predicate fzn_sort(array[int] of var int: x, array[int] of var int: y) =
    glasgow_sort(x, y);
