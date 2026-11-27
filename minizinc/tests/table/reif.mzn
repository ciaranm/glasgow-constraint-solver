include "table.mzn";

% An integer table in reified, half-reified and negated contexts (#1006). The
% standard library's fzn_table_int_reif enumerates the scope's domains into a
% bigger table with the control variable as an extra column, and hands that
% to fzn_table_int, so each of these reaches glasgow_table_int over one more
% variable than the model wrote, except the single-variable one, which the
% library turns into set_in_reif instead. Some rows hold values outside the
% scope's domains.
array[1..2] of var 1..2: x;
var bool: r;
constraint r <-> table(x, [| 1, 2 | 2, 2 | 3, 3 |]);

array[1..2] of var -1..0: y;
var bool: h;
constraint h -> table(y, [| -1, 0 | 0, 1 | 5, 5 |]);

array[1..2] of var 1..2: z;
constraint not table(z, [| 1, 1 | 2, 1 |]);

array[1..1] of var 1..4: w;
var bool: s;
constraint s <-> table(w, [| 2 | 4 |]);

solve satisfy;
output ["ENUMSOL: \(x) \(r) \(y) \(h) \(z) \(w) \(s)"];
