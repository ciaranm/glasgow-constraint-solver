% Maximising a negation: MiniZinc introduces the objective o with x + o = 0,
% which the front end posts as Equals{x, -o}, a view of the objective. The
% check after each solution used to spell the objective over that view while
% `min:` spelled it over o itself (issue #1206).
var 0..3: x;
var -3..3: z;
constraint x != z;
solve maximize -x;
output ["OPTSOL: " ++ show(-x)];
