% The five-mark Golomb ruler: the shortest ruler with five marks and all
% pairwise distances different has length 11. Variety (issue #1006): an
% optimisation over differences of the marks, with strictly_increasing and an
% all_different over introduced variables, and a symmetry-breaking constraint.
include "globals.mzn";

int: m = 5;
int: n = m * m;
array[1..m] of var 0..n: mark;
array[1..m * (m - 1) div 2] of var 1..n: gaps =
    [mark[j] - mark[i] | i in 1..m, j in i + 1..m];

constraint mark[1] = 0;
constraint strictly_increasing(mark);
constraint all_different(gaps);
constraint gaps[1] < gaps[m * (m - 1) div 2];

solve minimize mark[m];

output ["OPTSOL: \(mark[m])"];
