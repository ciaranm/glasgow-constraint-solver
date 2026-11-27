include "globals.mzn";

% The shapes a front end can misread for increasing and strictly_increasing
% (#1006), each of which reaches a builtin: a Boolean array indexed from 0; an
% enum-valued array indexed from -1; integer literals around a variable; a
% two-dimensional array, which the wrapper reads in row-major order; empty int
% and Boolean arrays, which the wrapper hands over unguarded; a single element
% indexed from 7; and strictly_increasing over an int array, over an
% enum-indexed array, and over a literal and a variable. decreasing_shapes.mzn
% has the decreasing forms.
array[0..2] of var bool: b;
constraint increasing(b);

enum Size = {S, M, L};
array[-1..0] of var Size: e;
constraint increasing(e);
constraint e[-1] = M;

var 1..3: m;
constraint increasing([1, m, 2]);

array[1..2, 0..1] of var 0..1: g;
constraint increasing(g);
constraint g[1, 1] = 1;

array[1..0] of var 1..3: x0;
constraint increasing(x0);
array[1..0] of var bool: b0;
constraint increasing(b0);

array[7..7] of var 1..2: x1;
constraint increasing(x1);
constraint x1[7] = m;

array[1..3] of var 2..4: s;
constraint strictly_increasing(s);
array[Size] of var 1..4: se;
constraint strictly_increasing(se);
constraint strictly_increasing([0, se[S]]);

solve satisfy;
output ["ENUMSOL: \(b) \(e) \(m) \(g) \(x1) \(s) \(se)"];
