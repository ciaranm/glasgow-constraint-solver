% Langford's problem L(2, 4): place two copies of each of 1..4 in a row of
% eight so that the copies of i have i numbers between them. Two solutions,
% 41312432 and its reverse. Variety (issue #1006): each pair is a two-term
% int_lin_eq with a different constant, which the reader recovers as Equals
% with an offset view.
include "globals.mzn";

int: k = 4;
array[1..k] of var 1..2 * k: first;
array[1..k] of var 1..2 * k: second;

constraint forall (i in 1..k) (second[i] = first[i] + i + 1);
constraint all_different(first ++ second);

solve satisfy;

output ["ENUMSOL: \(first) \(second)"];
