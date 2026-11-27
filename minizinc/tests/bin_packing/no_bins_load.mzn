include "globals.mzn";

% An item and no loads (#1006): as no_bins_capa.mzn, for the load form's own
% guard, which has to say false. The flattener decides it, so no solver runs.
array[1..1] of var 0..2: bin;

constraint bin_packing_load([], bin, [0]);

solve satisfy;

output ["ENUMSOL: \(bin)"];
