include "globals.mzn";

% Variable durations, heights, AND capacity: every non-start argument is a
% decision variable, exercising glasgow_cumulative's fully-variable path
% (issue #242's failing shape — the old mznlib fix()-erred at flatten time).
% The variable heights/capacity also stop MiniZinc's cumulative wrapper from
% short-circuiting into a disjunctive on the starts (see cumulativetest.mzn).
% Enumerated against MiniZinc's default solver.
int: n = 3;
array[1..n] of var 0..3: s;
array[1..n] of var 1..2: d;
array[1..n] of var 1..2: h;
var 2..3: c;

constraint cumulative(s, d, h, c);

% Force real interaction: total demand must exceed any single capacity value,
% and everything must fit in a tight horizon.
constraint sum(h) >= c + 1;
constraint forall(i in 1..n) (s[i] + d[i] <= 4);

solve satisfy;

output ["ENUMSOL: s=" ++ show(s) ++ " d=" ++ show(d) ++ " h=" ++ show(h) ++ " c=" ++ show(c) ++ "\n"];
