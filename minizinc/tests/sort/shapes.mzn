include "globals.mzn";

% The shapes a front end can misread for sort (#1006), each of which reaches the
% builtin: x and y with different index sets, neither from 1, and a variable
% repeated in x; two empty arrays with different index sets; a single element
% indexed from 5 against one indexed from 1, over different domains; integer
% literals and a repeated variable in x, so y has repeated values; an
% enum-indexed, enum-valued x; and the function form over an x indexed from 3.
array[0..2] of var 0..2: xa;
array[-1..1] of var 0..2: ya;
constraint sort(xa, ya);
constraint xa[0] = 2 /\ xa[1] = xa[2];

array[1..0] of var 0..2: x0;
array[3..2] of var 0..2: y0;
constraint sort(x0, y0);

array[5..5] of var 1..3: x1;
array[1..1] of var 2..4: y1;
constraint sort(x1, y1);

var 1..3: a;
array[1..3] of var 1..3: yd;
constraint sort([a, 2, a], yd);

enum Col = {R, G, B};
array[Col] of var Col: xe;
array[1..3] of var Col: ye;
constraint sort(xe, ye);
constraint xe[R] != R /\ xe[G] != G /\ xe[B] = B;

array[3..4] of var 1..2: xf;
array[int] of var int: yf = sort(xf);
constraint xf[3] = 2;

solve satisfy;
output ["ENUMSOL: \(xa) \(ya) \(x1) \(y1) \(a) \(yd) \(xe) \(ye) \(xf) \(yf)"];
