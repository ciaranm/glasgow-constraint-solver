include "alldifferent.mzn";

% Bound-split branching where each node flips a coin for which half to try
% first. Issue #568: both arms of that coin flip used to yield the same pair
% of conditions, so indomain_split_random silently behaved as "upper half
% first, always" and never exercised the randomised ordering at all. A
% complete search must enumerate the same solutions whichever way each coin
% lands, and the proof must still verify with the two split branches emitted
% in either order.
array[1..4] of var 1..4: x;

constraint alldifferent(x);
constraint x[1] < x[4];

solve :: int_search(x, first_fail, indomain_split_random) satisfy;

output ["ENUMSOL: x=\(x)\n"];
