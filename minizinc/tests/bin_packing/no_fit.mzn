include "globals.mzn";

% An item heavier than the capacity (#1006), so it fits in no bin and the
% model is unsatisfiable. The flattener does not see it, so BinPacking has to,
% with a proof. Negative bins, and an index set starting at 0.
array[0..2] of var -1..0: bin;

constraint bin_packing(2, bin, array1d(0..2, [1, 3, 0]));

solve satisfy;

output ["ENUMSOL: \(bin)"];
