include "globals.mzn";

% The motivating use for optional tasks: schedule as many as possible. Four
% tasks of length 2 and unit demand share a capacity-1 resource over t in 0..5,
% so at most three fit end to end and the fourth must be dropped.
%
% One constraint per model file, per the test conventions: independent
% constraints in one model multiply the search space for no extra coverage.
array[1..4] of int: lengths = [2, 2, 2, 2];
array[1..4] of int: heights = [1, 1, 1, 1];
int: capacity = 1;

array[1..4] of var opt 0..4: s;

constraint cumulative(s, lengths, heights, capacity);

var 0..4: scheduled;
constraint scheduled = sum(i in 1..4) (bool2int(occurs(s[i])));

solve maximize scheduled;

output ["OPTSOL: " ++ show(scheduled)];
