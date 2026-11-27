% Integer element in reified and half-reified contexts (#1006), where an index
% past the array makes the comparison false instead of cutting the index's
% domain: a parameter array indexed from 0 and an array of variables indexed
% from 5.
array[0..2] of int: p = array1d(0..2, [4, -1, 4]);
var -1..3: i;
var bool: r;
constraint r <-> p[i] = 4;

array[5..6] of var 1..2: x;
var 4..7: k;
var bool: h;
constraint h -> x[k] = 2;

solve satisfy;
output ["ENUMSOL: \(i) \(r) \(x) \(k) \(h)"];
