include "mdd.mzn";

% mdd in reified, half-reified and negated contexts (#1006), which go to the
% standard library's fzn_mdd_reif decomposition rather than to glasgow_mdd,
% but have to be able to get there. The one plain call does reach the builtin.
array[1..2] of var 0..1: x;
var bool: r;
constraint r <-> mdd(x, 3, [1, 2, 2], 3,
    [1, 1, 2], [{0}, {1, 2}, {1}], [2, 3, 0]);

array[1..2] of var 0..1: y;
var bool: h;
constraint h -> mdd(y, 2, [1, 2], 2, [1, 2], [{0, 2}, {1}], [2, 0]);

array[1..2] of var 1..2: z;
constraint not mdd(z, 2, [1, 2], 2, [1, 2], [{1}, {1, 2}], [2, 0]);

array[1..2] of var 1..2: w;
constraint mdd(w, 2, [1, 2], 2, [1, 2], [{2}, {1, 2}], [2, 0]);

solve satisfy;
output ["ENUMSOL: \(x) \(r) \(y) \(h) \(z) \(w)"];
