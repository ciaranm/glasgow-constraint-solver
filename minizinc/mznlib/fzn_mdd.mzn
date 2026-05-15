predicate glasgow_mdd(array[int] of var int: x,
                      int: N,
                      array[int] of int: level,
                      int: E,
                      array[int] of int: from,
                      array[int] of set of int: label,
                      array[int] of int: to);

predicate fzn_mdd(array [int] of var int: x,
                  int: N,
                  array [int] of int: level,
                  int: E,
                  array [int] of int: from,
                  array [int] of set of int: label,
                  array [int] of int: to) =
    glasgow_mdd(x, N, level, E, from, label, to);
