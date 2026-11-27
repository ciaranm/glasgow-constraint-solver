include "globals.mzn";

% bounded_dpath is dpath plus a weighted sum, so it too rides an existing
% wrapper down to the DPath propagator. The int-indexed spelling, whose nodes
% are 1..N.
int: N = 4;
int: E = 5;
array[1..E] of int: from = [1, 2, 1, 3, 2];
array[1..E] of int: to = [2, 3, 3, 4, 4];
array[1..E] of int: w = [1, 1, 5, 1, 7];
array[1..N] of var bool: ns;
array[1..E] of var bool: es;
var 1..N: s;
var 1..N: t;
var int: K;

constraint s = 1 /\ t = 4;
constraint bounded_dpath(N, E, from, to, w, s, t, ns, es, K);

solve minimize K;

output ["OPTSOL: " ++ show(K)];
