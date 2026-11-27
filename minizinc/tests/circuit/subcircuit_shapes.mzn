include "globals.mzn";

% As shapes.mzn, for subcircuit, whose redefinition passes the same offset:
% arrays indexed from -2, from 100 (with one node pinned on the tour and one
% off it) and over an enum, integer literals among the successors (node 1 is
% off the tour), and domains reaching past the index set. Subcircuit also has
% no trouble at the small sizes, so a single node, whose only solution is the
% empty tour, and an empty array, which never reaches the builtin and has to
% be guarded in the redefinition, are packed in here too.
array[-2..0] of var -2..0: neg;
array[100..103] of var 100..103: big;
enum City = {Ayr, Bute, Cupar};
array[City] of var City: tour;
array[5..5] of var 4..6: one;
array[1..0] of var 1..3: none;
var 1..3: u;
var 1..3: v;
array[0..2] of var -5..9: wide;

constraint subcircuit(neg);
constraint big[101] != 101 /\ big[103] = 103;
constraint subcircuit(big);
constraint tour[Ayr] != Ayr;
constraint subcircuit(tour);
constraint subcircuit(one);
constraint subcircuit(none);
constraint subcircuit([1, u, v]);
constraint wide[0] = 0;
constraint subcircuit(wide);

solve satisfy;

output ["ENUMSOL: \(neg) \(big) \(tour) \(one) \(u) \(v) \(wide)"];
