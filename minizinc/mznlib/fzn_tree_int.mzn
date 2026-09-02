include "fzn_tree_enum.mzn";

% The int-indexed spelling, whose nodes are 1..N and edges 1..E; the shared
% definition and the reason for it are in fzn_tree_enum.mzn.
predicate fzn_tree(int: N, int: E, array[int] of int: from, array[int] of int: to,
    var int: r, array[int] of var bool: ns, array[int] of var bool: es) =
    glasgow_tree([from[e] - 1 | e in 1..E], [to[e] - 1 | e in 1..E], r - 1,
                 [ns[n] | n in 1..N], [es[e] | e in 1..E]);
