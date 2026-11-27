include "globals.mzn";

% all_different and alldifferent_except over bools at the root, which reach
% the builtins. MiniZinc 2.9 coerces the bools to integers first; 2.10 and
% later hand the bool array to fzn_all_different_int as it is, which is the
% shape this pins for us, since a bool is a {0, 1} integer to fzn-glasgow.
% MiniZinc's default solver rejects that flattening (`Type error: integer
% literal expected`, Gecode 6.4.0 under MiniZinc 2.10.1 and 2.11.0), so the
% lane compares against the standard library's decompositions alone.
var bool: p;
var bool: q;
var bool: r;
var bool: s;
var bool: t;

constraint all_different([p, q]);
constraint all_different([r, true]);
constraint alldifferent_except([s, t, true, q], {1});

solve satisfy;

output ["ENUMSOL: \(p) \(q) \(r) \(s) \(t)"];
