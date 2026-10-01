include "globals.mzn";

% Empty and single-element arrays under reification and half-reification, and
% a reified negation of a single-element array. The standard library's reified
% increasing decomposition is wrong on an empty array, so redefinitions.mzn
% decides these lengths before reaching it (#1146). Negations of an empty array
% are covered by minizinc-decreasing-empty-not and
% minizinc-strictlydecreasing-empty-not at the top level, and by
% minizinc-decreasing-empty-halfnot under implication.
array[1..0] of var 1..3: e;
array[1..1] of var 1..3: o;
var bool: r1;
var bool: r2;
var bool: r3;
var bool: r4;
var bool: r5;
var bool: r6;
var bool: r7;

constraint r1 <-> decreasing(e);
constraint r2 -> decreasing(e);
constraint r3 <-> strictly_decreasing(e);
constraint r4 -> strictly_decreasing(e);
constraint r5 <-> decreasing(o);
constraint r6 -> strictly_decreasing(o);
constraint r7 <-> not strictly_decreasing(o);

solve satisfy;

output ["ENUMSOL: \(o) \(r1) \(r2) \(r3) \(r4) \(r5) \(r6) \(r7)"];
