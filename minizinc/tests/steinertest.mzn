include "globals.mzn";

% steiner is tree plus a weighted sum, so it reaches the Tree propagator through
% the stdlib's own wrapper rather than through an override of its own. The
% --fzn-pattern guard on glasgow_tree is what proves that, rather than assuming
% it. This is the int-indexed spelling, whose nodes are 1..N.
int: N = 4;
int: E = 4;
array[1..E] of int: from = [1, 2, 1, 3];
array[1..E] of int: to = [2, 3, 3, 4];
array[1..E] of int: w = [3, 1, 4, 1];
array[1..N] of var bool: ns;
array[1..E] of var bool: es;
var int: K;

constraint ns[1] /\ ns[4];
constraint steiner(N, E, from, to, w, ns, es, K);

solve minimize K;

output ["OPTSOL: " ++ show(K)];
