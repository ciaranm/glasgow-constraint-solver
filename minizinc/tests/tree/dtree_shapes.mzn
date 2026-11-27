include "globals.mzn";

% As shapes.mzn, for dtree, where the direction of each arc matters, so
% swapping from and to would show: enum nodes and arcs with a 2-cycle and a
% root over the enum; nodes from 50 and arcs from -2, with parallel arcs
% equated (so the builtin sees one variable twice), a self loop, and a root
% whose domain reaches past the nodes on both sides; and dsteiner, which
% reaches the builtin through the standard library's wrapper and the N-and-E
% spelling, with a root domain wider than 1..N.
enum Node = {P, Q, R};
enum Arc = {PQ, QP, QR, PR};
array[Arc] of Node: fa = [P, Q, Q, P];
array[Arc] of Node: ta = [Q, P, R, R];
array[Node] of var bool: nsa;
array[Arc] of var bool: esa;
var Node: ra;

array[-2..1] of int: fb = array1d(-2..1, [50, 50, 51, 51]);
array[-2..1] of int: tb = array1d(-2..1, [51, 51, 51, 52]);
array[50..52] of var bool: nsb;
array[-2..1] of var bool: esb;
var 45..55: rb;

array[1..3] of int: fd = [1, 2, 3];
array[1..3] of int: td = [2, 3, 1];
array[1..3] of int: wd = [1, 2, 4];
array[1..3] of var bool: nsd;
array[1..3] of var bool: esd;
var 0..4: rd;
var int: Kd;

constraint nsa[R] /\ ra != R;
constraint dtree(fa, ta, ra, nsa, esa);
constraint esb[-2] = esb[-1];
constraint dtree(fb, tb, rb, nsb, esb);
constraint nsd[2] /\ nsd[3];
constraint dsteiner(3, 3, fd, td, wd, rd, nsd, esd, Kd);

solve satisfy;

output ["ENUMSOL: \(ra) \(nsa) \(esa) | \(rb) \(nsb) \(esb) | \(rd) \(nsd) \(esd) \(Kd)"];
