include "regular.mzn";

% More of the shapes fzn-glasgow's regular translation can misread (#1006),
% after start.mzn's start states. Regular is keyed by the symbol values 1..S
% it is given, and a FlatZinc transition to 0 means "no transition".

% Variables whose domains reach past the alphabet 1..S on both sides, so the
% values -1, 0 and 3 must be ruled out; zeros (the fail state) in the table;
% a state (3) that no transition reaches, which is final, so it must not
% matter; and the sequence indexed from 0.
array[0..2] of var -1..3: a;
array[1..3, 1..2] of int: da = [| 2, 1 | 0, 1 | 3, 3 |];
constraint regular(a, 3, 2, da, 1, {1, 3});

% A sequence of length 1.
array[1..1] of var 1..3: b;
constraint regular(b, 2, 3, [| 2, 0, 2 | 2, 2, 2 |], 1, {2});

% A one-state automaton over a sequence holding a variable twice and a
% constant.
var 1..3: c;
constraint regular([c, 2, c], 1, 3, [| 1, 1, 0 |], 1, {1});

solve satisfy;
output ["ENUMSOL: \(a) \(b) \(c)"];
