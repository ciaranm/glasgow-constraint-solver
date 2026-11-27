include "globals.mzn";

% A count of 0 for an array that is not empty. The stdlib wrapper only
% special-cases the empty array, so this reaches glasgow_nvalue as it is:
% unsatisfiable, and the proof has to say so.
var 0..1: a;
var 0..1: b;

constraint nvalue(0, [a, b]);

solve satisfy;

output ["ENUMSOL: \(a) \(b)"];
