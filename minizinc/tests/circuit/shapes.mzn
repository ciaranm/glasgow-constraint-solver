include "globals.mzn";

% circuit's values are indices into its own array, and FlatZinc arrays are
% 1-based, so fzn_circuit.mzn passes min(index_set(x)) as an offset and
% fzn-glasgow applies it as a view (#1006, after #987). Each call here starts
% somewhere a fixed offset would get wrong: at a negative value, at 100, at an
% enum's first value, and at 0 with successor domains reaching well past the
% index set on both sides. Two more: integer literals among the successors of an
% array indexed from -1, which only fit if the constants are shifted along with
% the variables, and successor domains with holes. single.mzn and empty.mzn have
% the sizes the references disagree on.
array[-2..1] of var -2..1: neg;
array[100..102] of var 100..102: big;
enum City = {Ayr, Bute, Cupar};
array[City] of var City: tour;
var -1..2: u;
var -1..2: v;
array[0..2] of var -5..9: wide;
var {2, 4}: h1;
var 1..4: h2;
var {1, 4}: h3;
var {1, 3}: h4;

constraint circuit(neg);
constraint circuit(big);
constraint circuit(tour);
constraint circuit(array1d(-1..2, [1, u, 2, v]));
constraint circuit(wide);
constraint circuit([h1, h2, h3, h4]);

solve satisfy;

output ["ENUMSOL: \(neg) \(big) \(tour) \(u) \(v) \(wide) \([h1, h2, h3, h4])"];
