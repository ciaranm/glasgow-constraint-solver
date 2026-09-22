include "globals.mzn";

% inverse's values are indices into the other array, so each of these reaches
% the builtin with starts the front end must read off the model (issue #1006,
% after #987; inversesoffset has two arrays starting at different places). Here:
% the enum-typed form over two different enums, which is what inverse is usually
% written for; an array that is its own inverse, which is how the stdlib's own
% symmetric_all_different decomposes, and hands Inverse the same variables
% twice; integer literals at a position that only fits at the right start; and
% two arrays made of the same three variables in a different order.
% inversesnegative has the shapes MiniZinc's default solver cannot run.
enum Worker = {Alice, Bob, Carol};
enum Job = {Cook, Drive, Sweep};
array[Worker] of var Job: does;
array[Job] of var Worker: done_by;
array[0..2] of var 0..2: self;
var 5..7: a;
var 5..7: b;
array[5..7] of var 0..2: g;
var 1..3: p;
var 1..3: q;
var 1..3: r;

constraint inverse(does, done_by);
constraint does[Alice] != Cook;
constraint inverse(self, self);
constraint inverse(array1d(0..2, [a, 7, b]), g);
constraint inverse([p, q, r], [q, r, p]);

solve satisfy;

output ["ENUMSOL: \(does) \(done_by) \(self) \(a) \(b) \(g) \(p) \(q) \(r)"];
