include "globals.mzn";

% The shapes a front end can misread for value_precede (#1006), each of which
% reaches the builtin: s = t, where t then cannot occur at all, since its first
% occurrence has no earlier s; an s outside every domain, which forbids t, over
% an x indexed from 0; a t outside every domain, which says nothing; an empty
% x; negative values with s > t, over integer literals and a repeated variable
% indexed from -2; and an enum-indexed, enum-valued x.
array[1..2] of var 1..3: xa;
constraint value_precede(2, 2, xa);
constraint xa[1] = xa[2];

array[0..2] of var -1..1: xb;
constraint value_precede(5, -1, xb);
constraint xb[0] != 0 /\ xb[1] = 1;

array[1..2] of var 0..1: xc;
constraint value_precede(0, 4, xc);
constraint xc[1] = xc[2];

array[1..0] of var 1..3: x0;
constraint value_precede(1, 2, x0);

var -3..-1: a;
var -3..-1: b;
constraint value_precede(-1, -3, array1d(-2..1, [b, a, -2, a]));

enum Col = {R, G, B};
array[Col] of var Col: xf;
constraint value_precede(B, G, xf);
constraint xf[R] != R /\ xf[G] != R;

solve satisfy;
output ["ENUMSOL: \(xa) \(xb) \(xc) \(a) \(b) \(xf)"];
