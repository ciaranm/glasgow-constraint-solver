include "globals.mzn";

% A one-node circuit, indexed from 5 with a domain either side of it. Glasgow
% and Gecode both take the self loop as the one-node tour, deliberately (#254,
% #1319), where the standard library's decomposition posts x[i] != i and so
% finds nothing; see dev_docs/constraints/circuit.md. The offset still has to
% be 5: assuming 1 would read the self loop as successor 4 of a one-element
% array, which is no solution at all.
array[5..5] of var 4..6: one;

constraint circuit(one);

solve satisfy;

output ["ENUMSOL: \(one)"];
