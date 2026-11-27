include "globals.mzn";

int: n;
array[1..n, 1..n] of int: distance;
array[1..n] of var 1..n: tour;
var int: cost = sum(i in 1..n)(distance[i, tour[i]]);
constraint circuit(tour);
solve minimize cost;
n = 5;
distance = [|0, 6, 4, 5, 8
            |6, 0, 4, 7, 6
            |4, 4, 0, 3, 4
            |5, 7, 3, 0, 5
            |8, 6, 4, 5, 0|];
output ["OPTSOL: " ++ show(cost) ++ "\n" ++ "tour = " ++ show(tour)];
