include "globals.mzn";

% No items, for all three forms (#1006). With bins to put them in, the
% capacity form reaches its builtin with no items, and so does the load form,
% whose loads must then all be 0. With no bins either, each redefinition's
% length guard has to answer without taking the min of an empty index set,
% and so does the single-capacity form's, without taking lb_array of no
% items. Native Gecode's redefinitions take those bounds unguarded and report
% an error, so this has its own model.
array[1..0] of var 0..2: none;
array[1..0] of int: nw = [];
array[-2..-1] of var 0..1: load;
var 0..1: z;

constraint bin_packing(0, none, nw);
constraint bin_packing_capa(array1d(3..4, [1, 0]), none, nw);
constraint bin_packing_capa([], none, nw);
constraint bin_packing_load(load, none, nw);
constraint bin_packing_load([], none, nw);

solve satisfy;

output ["ENUMSOL: \(load) \(z)"];
