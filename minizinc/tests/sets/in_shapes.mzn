% set_in and set_in_reif with sets that have holes, sets of a single value,
% and sets reaching past the variable's domain (#1006). fzn-glasgow posts the
% set's bounds and then one constraint per gap, so the holes are what it can
% get wrong. MiniZinc turns `x in S` at the top level into a domain rather
% than set_in, so the two set_in calls are written as the builtin directly;
% the reified, half-reified and negated memberships reach set_in_reif.
var -3..5: x;
constraint set_in(x, {-5, -2, 0, 1, 3, 4, 7});
var 0..4: y;
constraint set_in(y, {2});

var bool: r;
constraint r <-> x in {-2, 1, 4};
var bool: h;
constraint h -> x in {0, 5};
var bool: n;
constraint n <-> not (x in {1} union 3..4);
var bool: g;
constraint set_in_reif(y, {-1} union 2..3, g);
var bool: k;
constraint set_in_reif(x, {3}, k);

solve satisfy;
output ["ENUMSOL: \(x) \(y) \(r) \(h) \(n) \(g) \(k)"];
