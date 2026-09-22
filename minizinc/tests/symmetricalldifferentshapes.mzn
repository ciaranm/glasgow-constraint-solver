include "globals.mzn";

% symmetric_all_different's values are indices into its own array, so each of
% these reaches the builtin with a start the front end must read off the model
% rather than assume (issue #1006, after #987): an array indexed from 1000, a
% single element indexed from 5 over a domain reaching both sides of it, integer
% literals at known positions of an array indexed from 0 -- which only fit the
% involution at the right start -- and a domain with holes that reaches past the
% index set on both sides. symmetricalldifferentnegative has the shapes MiniZinc's
% default solver cannot run.
array[1000..1002] of var 999..1003: big;
array[5..5] of var 3..7: one;
var 0..3: a;
var 0..3: b;
array[0..2] of var {-3, 0, 1, 2, 7}: holes;

constraint symmetric_all_different(big);
constraint symmetric_all_different(one);
constraint symmetric_all_different(array1d(0..3, [a, 2, 1, b]));
constraint symmetric_all_different(holes);

solve satisfy;

output ["ENUMSOL: \(big) \(one) \(a) \(b) \(holes)"];
