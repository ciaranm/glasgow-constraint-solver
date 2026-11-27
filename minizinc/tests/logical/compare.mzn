% The comparison-like Boolean builtins, plain and reified, with constants and
% repeated variables (#1006). Written as direct calls, which MiniZinc passes
% through untouched. (bool_eq between two variables never reaches a solver:
% MiniZinc unifies the two instead.)
var bool: p; var bool: q; var bool: s; var bool: u; var bool: w;
var bool: k1; var bool: k2;
constraint bool_le(p, q);
constraint bool_le(w, true);
constraint bool_lt(k1, k2);
% The two-argument xor, which MiniZinc passes on as bool_xor(p, s, true).
constraint bool_xor(p, s);

var bool: e1; var bool: e2; var bool: e3; var bool: l1; var bool: l2;
var bool: t1; var bool: t2; var bool: t3; var bool: o1; var bool: o2;
var bool: a1; var bool: x1; var bool: x2; var bool: n1;
constraint bool_eq_reif(p, q, e1);
constraint bool_eq_reif(p, p, e2);
constraint bool_eq_reif(q, true, e3);
constraint bool_le_reif(q, p, l1);
constraint bool_le_reif(s, false, l2);
constraint bool_lt_reif(p, s, t1);
constraint bool_lt_reif(q, q, t2);
constraint bool_lt_reif(false, u, t3);
constraint bool_or(p, s, o1);
constraint bool_or(false, w, o2);
constraint bool_and(true, s, a1);
constraint bool_xor(u, w, x1);
constraint bool_xor(q, true, x2);
constraint bool_not(s, n1);

% bool2int into a variable with a wider domain, and from a constant.
var -1..3: i; var -1..3: j;
constraint bool2int(p, i);
constraint bool2int(true, j);

solve satisfy;
output ["ENUMSOL: \([p, q, s, u, w, k1, k2]) ",
    "\([e1, e2, e3, l1, l2, t1, t2, t3, o1, o2, a1, x1, x2, n1]) \(i) \(j)"];
