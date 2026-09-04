% As twotermlineq, for `x != y`: MiniZinc gives us a two-term int_lin_ne, and
% the reader recovers NotEquals. Domains are kept small because these
% constraints are loose, so the enumeration stays a few hundred solutions.
var -2..2: a;
var -2..2: b;
var -2..2: c;
var -2..2: d;
var -2..2: s;

constraint a - b != 1;   % coefficients [1, -1]
constraint a + b != 0;   % coefficients [1, 1]
constraint -c + d != 2;  % coefficients [-1, 1]
constraint -c - d != -1; % coefficients [-1, -1]
constraint a + c != s;   % variable right-hand side: not two terms

solve satisfy;

output ["ENUMSOL: " ++ show(a) ++ " " ++ show(b) ++ " " ++ show(c) ++ " " ++ show(d) ++ " " ++ show(s)];
