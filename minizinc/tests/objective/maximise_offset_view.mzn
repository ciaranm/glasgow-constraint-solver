% Maximising 3 - z where z = 2 - x (issue #1006). The flattener introduces the
% objective o with int_lin_eq([-1, -1], [z, o], -3), which the reader recovers
% as Equals between o and the negated, offset view -z + 3, after dividing
% through by a negative first coefficient; z = 2 - x is recovered the same way
% with [1, 1]. maximize_negation.mzn is the same without the offsets (issue
% #1206).
var -6..-1: x;
var -6..6: z;

constraint abs(x) != 1;
constraint z = 2 - x;
constraint z mod 4 != 0;

solve maximize 3 - z;

output ["OPTSOL: \(3 - z)"];
