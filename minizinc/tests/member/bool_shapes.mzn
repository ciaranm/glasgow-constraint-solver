include "globals.mzn";

% member over bools, which reaches its own builtin, glasgow_member_bool
% (#1006): a constant searched-for value, true and false, with a literal of the
% other polarity beside the variable, and with one of the same polarity, which
% makes it hold whatever the variable is; a variable searched-for value over an
% array of two variables, and over a single element indexed from 3; and a
% two-dimensional array.
var bool: p;
var bool: q;
var bool: r;
var bool: s;
array[3..3] of var bool: t;
var bool: u;
array[1..2, 1..2] of var bool: g;

constraint member([p, false], true);
constraint member([q, r], s);
constraint member(t, u);
constraint member([false, s], false);
constraint member(g, false) /\ g[1, 1] /\ g[2, 2];

solve satisfy;

output ["ENUMSOL: \(p) \(q) \(r) \(s) \(t) \(u) \(g)"];
