% y = -x becomes Equals{y, -x}, a view of the objective, with x maximised
% (issue #1206).
var 0..3: x;
var -3..3: y;
var -3..3: z;
constraint y = -x;
constraint y != z;
solve maximize x;
output ["OPTSOL: " ++ show(x)];
