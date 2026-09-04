% MiniZinc rewrites `x = y` between two variables into a two-term int_lin_eq
% rather than emitting int_eq, so the FlatZinc reader recovers the shape and
% posts Equals (which intersects domains, where the generic linear equality is
% bounds(Z) only). Every unit-coefficient sign pattern the rewrite has to
% normalise appears here, plus a variable right-hand side, which is three terms
% after it is moved across and so must fall through to LinearEquality.
var -4..4: a;
var -4..4: b;
var -4..4: c;
var -4..4: d;
var -4..4: e;
var -4..4: f;
var -4..4: g;
var -4..4: h;
var -4..4: s;

constraint a - b = 2;   % coefficients [1, -1]
constraint c + d = -1;  % coefficients [1, 1]
constraint -e + f = 3;  % coefficients [-1, 1]
constraint -g - h = 0;  % coefficients [-1, -1]
constraint a + e = s;   % variable right-hand side: not two terms

solve satisfy;

output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c) ++ " " ++ show(d) ++ " " ++
    show(e) ++ " " ++ show(f) ++ " " ++ show(g) ++ " " ++ show(h) ++ " " ++ show(s)];
