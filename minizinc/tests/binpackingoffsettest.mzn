include "globals.mzn";

% The bin offset, which the redefinitions pass and fzn_glasgow applies as a
% view. binpackingtest.mzn covers the ordinary 1-based case, where the offset is
% 1 and a mistake in either direction is easy to miss; these two are the ones
% that pin it down.
%
% First: bin_packing_capa with a capacity array that is neither 1-based nor
% 0-based, so the offset is min(index_set(c)) = 5 and nothing about the model is
% consistent with assuming 1.
array[1..4] of int: w = [3, 2, 2, 1];
array[5..7] of int: c = array1d(5..7, [4, 4, 4]);
array[1..4] of var 5..7: bin;

constraint bin_packing_capa(c, bin, w);

% Second: the single-capacity bin_packing form, whose offset is lb_array(bin2)
% rather than an index set at all -- a different code path in the redefinition,
% and one no test reached before.
array[1..3] of int: w2 = [2, 2, 1];
array[1..3] of var 3..5: bin2;

constraint bin_packing(3, bin2, w2);

solve satisfy;

output ["ENUMSOL: " ++ join(" ", [show(bin[i]) | i in 1..4]) ++ " | " ++ join(" ", [show(bin2[i]) | i in 1..3])];
