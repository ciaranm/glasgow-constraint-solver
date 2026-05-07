predicate glasgow_knapsack(array[int] of int: w, array[int] of int: p,
    array[int] of var int: x, var int: W, var int: P);
predicate fzn_knapsack(array[int] of int: w, array[int] of int: p,
    array[int] of var int: x, var int: W, var int: P) =
    glasgow_knapsack(w, p, x, W, P);
