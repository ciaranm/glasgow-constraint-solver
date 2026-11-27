% Minimising under a search annotation that goes the wrong way for the
% objective (issue #1006): indomain_max tries the largest values first, so the
% first solutions are poor and the solver has to keep improving. The objective
% is a sum of squares, each an int_times on the same variable twice.
array[1..4] of var -3..3: x;

constraint sum(x) >= 2;
constraint forall (i in 1..3) (x[i] != x[i + 1]);

solve :: int_search(x, input_order, indomain_max) minimize sum (i in 1..4) (x[i] * x[i]);

output ["OPTSOL: \(sum (i in 1..4) (x[i] * x[i]))"];
