include "globals.mzn";

% Shapes of dag that fzn_dag.mzn shifts by min(index_set(ns)) (#1006): enum
% nodes and arcs with a 2-cycle whose arcs are equated (so the builtin sees one
% variable twice, and neither can be used), a self loop and a pair of parallel
% arcs; nodes from -3 and arcs from 0 round a 3-cycle; and a single node at 20
% with no arcs. subgraph is posted alongside the two with arcs, as in
% basic.mzn, so that the standard library's reading of dag is the documented
% one (see dev_docs/minizinc.md); its count is part of the guard.
enum Node = {P, Q, R};
enum Arc = {PQ, QP, QQ, QR1, QR2};
array[Arc] of Node: fa = [P, Q, Q, Q, Q];
array[Arc] of Node: ta = [Q, P, Q, R, R];
array[Node] of var bool: nsa;
array[Arc] of var bool: esa;

array[0..2] of int: fb = array1d(0..2, [-3, -2, -1]);
array[0..2] of int: tb = array1d(0..2, [-2, -1, -3]);
array[-3..-1] of var bool: nsb;
array[0..2] of var bool: esb;

array[1..0] of int: fc = [];
array[1..0] of int: tc = [];
array[20..20] of var bool: nsc;
array[1..0] of var bool: esc;

constraint nsa[Q] /\ nsa[R] /\ esa[PQ] = esa[QP];
constraint dag(fa, ta, nsa, esa);
constraint subgraph(fa, ta, nsa, esa);
constraint nsb[-3] /\ nsb[-1];
constraint dag(fb, tb, nsb, esb);
constraint subgraph(fb, tb, nsb, esb);
constraint dag(fc, tc, nsc, esc);

solve satisfy;

output ["ENUMSOL: \(nsa) \(esa) | \(nsb) \(esb) | \(nsc)"];
