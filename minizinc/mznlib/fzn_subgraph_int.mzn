include "fzn_subgraph_enum.mzn";

% The int-indexed spelling, whose nodes are 1..N and edges 1..E; the shared
% definition and the reason for it are in fzn_subgraph_enum.mzn.
predicate fzn_subgraph(int: N, int: E, array[int] of int: from, array[int] of int: to,
    array[int] of var bool: ns, array[int] of var bool: es) =
    glasgow_subgraph([from[e] - 1 | e in 1..E], [to[e] - 1 | e in 1..E],
                     [ns[n] | n in 1..N], [es[e] | e in 1..E]);
