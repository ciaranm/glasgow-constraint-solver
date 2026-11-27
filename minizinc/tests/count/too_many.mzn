include "globals.mzn";

% A constant count larger than the array, which reaches glasgow_count_eq as it
% is: unsatisfiable, and the proof has to say so.
var 0..1: a;
var 0..1: b;

constraint exactly(3, [a, b], 1);

solve satisfy;

output ["ENUMSOL: \(a) \(b)"];
