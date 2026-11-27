% Element on parameter arrays indexed from 0, from a negative value and from
% somewhere large (#1006). FlatZinc arrays are 1-based, so MiniZinc shifts the
% index into a fresh variable defined by a two-term int_lin_eq, which
% fzn-glasgow posts as an equality with an offset view, and array_int_element
% then applies its own offset of 1 on top. Each index variable's domain
% reaches past its array, which at the top level MiniZinc cuts down to the
% index set.
array[0..3] of int: p0 = array1d(0..3, [5, 7, 7, 2]);
var -5..5: i0;
var int: v0;
constraint v0 = p0[i0];

array[-3..-1] of int: pn = array1d(-3..-1, [-4, 0, 9]);
var -5..5: in_;
var int: vn;
constraint vn = pn[in_];

array[1000..1002] of int: pl = array1d(1000..1002, [3, 1, 3]);
var 999..1003: il;
var int: vl;
constraint vl = pl[il];

solve satisfy;
output ["ENUMSOL: \(i0) \(v0) \(in_) \(vn) \(il) \(vl)"];
