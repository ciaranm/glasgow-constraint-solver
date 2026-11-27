include "globals.mzn";

% The shapes a front end hands the three bin_packing forms (#1006), each
% reaching glasgow_bin_packing_capa or glasgow_bin_packing_load, which the
% lane counts. The bins are values, and BinPacking numbers them from 0, so
% each redefinition passes an offset: lb_array(bin) for the single-capacity
% form, and the first index of the capacity or load array for the others.
% offset.mzn has offsets of 5 and 3 and load.mzn one of 0; these are negative.
% Every item's domain stays inside the bins, which BinPacking needs (#1347).

% Single capacity, with bins {-2, 0}: the offset is -2, and bin -1 is in the
% capacity array the redefinition builds although no item can take it. A
% zero-weight item, and an index set starting at 0.
array[0..2] of var {-2, 0}: bin;
constraint bin_packing(2, bin, array1d(0..2, [2, 0, 1]));

% Per-bin capacities indexed from -1, with a zero capacity that only
% zero-weight items can use. A variable repeated with different weights, an
% integer-literal bin, a bin that is an expression, and an item index set
% that is not the capacities'.
array[-1..1] of int: c = array1d(-1..1, [0, 2, 2]);
var -1..1: v;
var -1..1: t;
constraint bin_packing_capa(c, array1d(4..8, [v, 1, v, bin[1] + 1, t]),
    array1d(4..8, [1, 0, 0, 1, 0]));

% Variable loads indexed from -1, and a zero-weight item.
array[-1..1] of var 0..3: load;
array[1..3] of var -1..1: b2;
constraint bin_packing_load(load, b2, [2, 0, 1]);
constraint b2[1] != 0 /\ b2[2] = b2[3];

% A reified call, which has to reach the standard library's decomposition.
var bool: rb;
constraint rb <-> bin_packing_capa([1, 1], [v + 2, bin[2] + 3], [1, 1]);

solve satisfy;

output ["ENUMSOL: \(bin) \(v) \(t) \(b2) \(load) \(rb)"];
