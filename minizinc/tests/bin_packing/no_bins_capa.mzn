include "globals.mzn";

% An item and no bins (#1006): the redefinition's guard for an empty capacity
% array has to say false, since the item has nowhere to go, even though it
% weighs nothing. The flattener decides it, so no solver runs. Native
% Gecode's redefinition takes the min of the empty index set and reports an
% error instead.
array[1..1] of var 0..2: bin;

constraint bin_packing_capa([], bin, [0]);

solve satisfy;

output ["ENUMSOL: \(bin)"];
