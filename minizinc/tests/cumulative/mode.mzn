include "globals.mzn";

% MRCPSP-shaped instance: each task picks a mode, and the mode determines
% both its duration and its resource demand, so the cumulative is posted with
% variable durations AND variable demands (exercising glasgow_cumulative's
% variable d/r path end to end). Heights are variable, so MiniZinc's
% cumulative wrapper cannot short-circuit into a disjunctive.
int: n = 2;
set of int: TASK = 1..n;
set of int: MODE = 1..2;

array[MODE] of int: dur = [2, 1];
array[MODE] of int: dem = [1, 2];

array[TASK] of var MODE: mode;
array[TASK] of var 0..4: s;
array[TASK] of var 1..2: d = [dur[mode[i]] | i in TASK];
array[TASK] of var 1..2: r = [dem[mode[i]] | i in TASK];
int: capacity = 2;

constraint cumulative(s, d, r, capacity);

% Keep the search space small but non-trivial.
constraint forall(i in TASK) (s[i] + d[i] <= 5);

solve satisfy;

output ["ENUMSOL: s=" ++ show(s) ++ " mode=" ++ show(mode) ++ "\n"];
