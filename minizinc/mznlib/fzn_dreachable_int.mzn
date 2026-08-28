include "fzn_dreachable_enum.mzn";

% The int-indexed spelling; see fzn_dreachable_enum.mzn.
predicate fzn_dreachable(int: N, int: E, array[int] of int: from, array[int] of int: to,
    var int: r, array[int] of var bool: ns, array[int] of var bool: es) =
    glasgow_dreachable([from[e] - 1 | e in 1..E], [to[e] - 1 | e in 1..E], r - 1,
                       [ns[n] | n in 1..N], [es[e] | e in 1..E]);
