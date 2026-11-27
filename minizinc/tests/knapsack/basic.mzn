include "globals.mzn";

array[1..4] of int: w = [3, 4, 5, 7];
array[1..4] of int: p = [2, 3, 4, 5];
array[1..4] of var 0..1: x;
var 0..20: W;
var 0..20: P;

constraint knapsack(w, p, x, W, P);
constraint W <= 12;

solve maximize P;

output ["OPTSOL: " ++ show(P)];
