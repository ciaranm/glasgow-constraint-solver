include "globals.mzn";

% As shapes.mzn, for dreachable, where the direction of each edge matters, so
% swapping from and to anywhere would show: enum nodes and edges with a 2-cycle
% and a root over the enum; nodes from -1 and edges from 3, with parallel arcs,
% a self loop and a root whose domain reaches past the nodes; and the
% N-and-E spelling with the root fixed at the head of every arc.
enum Node = {P, Q, R};
enum Arc = {PQ, QP, QR};
array[Arc] of Node: fa = [P, Q, Q];
array[Arc] of Node: ta = [Q, P, R];
array[Node] of var bool: nsa;
array[Arc] of var bool: esa;
var Node: ra;

array[3..6] of int: fb = array1d(3..6, [-1, -1, 0, 1]);
array[3..6] of int: tb = array1d(3..6, [0, 0, 0, 0]);
array[-1..1] of var bool: nsb;
array[3..6] of var bool: esb;
var -4..4: rb;

array[1..2] of int: fc = [1, 2];
array[1..2] of int: tc = [3, 3];
array[1..3] of var bool: nsc;
array[1..2] of var bool: esc;

constraint nsa[R];
constraint dreachable(fa, ta, ra, nsa, esa);
constraint dreachable(fb, tb, rb, nsb, esb);
constraint dreachable(3, 2, fc, tc, 3, nsc, esc);

solve satisfy;

output ["ENUMSOL: \(ra) \(nsa) \(esa) | \(rb) \(nsb) \(esb) | \(nsc) \(esc)"];
