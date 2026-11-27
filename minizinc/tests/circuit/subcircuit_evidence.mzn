include "globals.mzn";

% 1-based, so this is the other half of the index-shift check, and node 1 is
% pinned onto the tour. That pin is what gives the propagator an evidence node:
% without one, no chain of fixed successors can be stopped from closing, because
% a closed tour with every other node opting out is a perfectly good solution.
% This is the case the C++ scenario test drives directly; here it has to survive
% the whole frontend.
array[1..5] of var 1..5: succ;

constraint subcircuit(succ);
constraint succ[1] != 1;

solve satisfy;

output ["ENUMSOL: " ++ show(succ)];
