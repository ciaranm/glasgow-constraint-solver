include "fzn_dpath_enum.mzn";

% The int-indexed spelling, whose nodes are 1..N and edges 1..E; the shared
% definition and the reason for it are in fzn_dpath_enum.mzn.
predicate fzn_dpath(int: N, int: E, array[int] of int: from, array[int] of int: to,
    var int: s, var int: t, array[int] of var bool: ns, array[int] of var bool: es) =
    glasgow_dpath([from[e] - 1 | e in 1..E], [to[e] - 1 | e in 1..E], s - 1, t - 1,
                  [ns[n] | n in 1..N], [es[e] | e in 1..E]);
