include "globals.mzn";

% Three bins of capacity 4, four items of sizes 3, 2, 2, 1.
% Exercises fzn_bin_packing_capa via the per-bin constant capacities form.
array[1..4] of int: w = [3, 2, 2, 1];
array[1..3] of int: c = [4, 4, 4];
array[1..4] of var 1..3: bin;

constraint bin_packing_capa(c, bin, w);

solve satisfy;

output ["ENUMSOL: " ++ join(" ", [show(bin[i]) | i in 1..4])];
