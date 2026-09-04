include "globals.mzn";

% fzn_bin_packing_load, which no MiniZinc test reached before: it is the form
% that carries variable loads, and it shifts the bins while leaving the load
% array alone, because load is indexed by bin rather than valued in bins.
%
% The load array is 0-based so the offset is 0 -- the one value that a shift
% applied in the wrong direction still gets right for the capa form, and so the
% case worth having alongside binpackingoffsettest.mzn's non-zero offsets.
array[1..4] of int: w = [3, 2, 2, 1];
array[0..2] of var 0..8: load;
array[1..4] of var 0..2: bin;

constraint bin_packing_load(load, bin, w);

solve satisfy;

output ["ENUMSOL: " ++ join(" ", [show(bin[i]) | i in 1..4]) ++ " | " ++ join(" ", [show(load[b]) | b in 0..2])];
