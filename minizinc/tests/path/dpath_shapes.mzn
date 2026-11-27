include "globals.mzn";

% As shapes.mzn, for dpath, where the direction of each arc matters, so
% swapping from and to, or the source and the target, would show: enum nodes
% with arcs from 0, a 2-cycle and a source and target over the enum; nodes from
% -3 and arcs from 2, with parallel arcs equated (so the builtin sees one
% variable twice), a self loop, and a source and target whose domains reach
% past the nodes; bounded_dpath over nodes from 0 with the source a variable;
% and the N-and-E spelling over a directed 3-cycle.
enum Stop = {A, B, C};
array[0..3] of Stop: fa = array1d(0..3, [A, B, B, A]);
array[0..3] of Stop: ta = array1d(0..3, [B, A, C, C]);
array[Stop] of var bool: nsa;
array[0..3] of var bool: esa;
var Stop: sA;
var Stop: tA;

array[2..5] of int: fb = array1d(2..5, [-3, -3, -2, -2]);
array[2..5] of int: tb = array1d(2..5, [-2, -2, -2, -1]);
array[-3..-1] of var bool: nsb;
array[2..5] of var bool: esb;
var -9..9: sB;
var -9..9: tB;

array[1..3] of int: fd = [0, 1, 0];
array[1..3] of int: td = [1, 2, 2];
array[1..3] of int: wd = [1, 1, 5];
array[0..2] of var bool: nsd;
array[1..3] of var bool: esd;
var 0..2: sd;
var int: Kd;

array[1..3] of int: fc = [1, 2, 3];
array[1..3] of int: tc = [2, 3, 1];
array[1..3] of var bool: nsc;
array[1..3] of var bool: esc;
var 1..3: tC;

constraint nsa[C];
constraint dpath(fa, ta, sA, tA, nsa, esa);
constraint esb[2] = esb[3];
constraint dpath(fb, tb, sB, tB, nsb, esb);
constraint bounded_dpath(fd, td, wd, sd, 2, nsd, esd, Kd);
constraint dpath(3, 3, fc, tc, 2, tC, nsc, esc);

solve satisfy;

output ["ENUMSOL: \(sA) \(tA) \(nsa) \(esa) | \(sB) \(tB) \(nsb) \(esb) | \(sd) \(nsd) \(esd) \(Kd) | \(tC) \(nsc) \(esc)"];
