include "globals.mzn";

% Indexed from 0 on purpose, as circuittest.mzn is: the FlatZinc subcircuit
% predicate is defined over index_set(x) with successor values in that same set,
% so a 0-based array must not be shifted as if it were 1-based.
%
% Four nodes is the smallest size that says anything beyond all-different: with
% three you cannot fit two disjoint cycles, so every permutation is a subcircuit.
% Twenty-one of the twenty-four permutations are solutions -- the three products
% of two 2-cycles are not -- and the identity is among them, being the empty
% subcircuit.
array[0..3] of var 0..3: succ;

constraint subcircuit(succ);

solve satisfy;

output ["ENUMSOL: " ++ show(succ)];
