include "fzn_path_enum.mzn";

% The int-indexed spelling, whose nodes are 1..N and edges 1..E; the shared
% definition and the reason for it are in fzn_path_enum.mzn.
predicate fzn_path(int: N, int: E, array[int] of int: from, array[int] of int: to,
    var int: s, var int: t, array[int] of var bool: ns, array[int] of var bool: es) =
    glasgow_path([from[e] - 1 | e in 1..E], [to[e] - 1 | e in 1..E], s - 1, t - 1,
                 [ns[n] | n in 1..N], [es[e] | e in 1..E]);
