include "globals.mzn";

% Shapes of subgraph that the redefinitions shift (#1006): the four-argument
% spelling reaches fzn_subgraph_enum.mzn, which subtracts min(index_set(ns)),
% and the six-argument one fzn_subgraph_int.mzn, which subtracts 1. Here: enum
% nodes and edges with a pair of parallel edges and a self loop; nodes from -2
% and edges from 3, with two node variables equated (so the builtin sees one
% variable twice); the six-argument spelling with no edges; and the
% six-argument spelling with Boolean literals among the node and edge
% variables.
enum Node = {P, Q};
enum Edge = {PQ1, PQ2, QQ};
array[Edge] of Node: fa = [P, P, Q];
array[Edge] of Node: ta = [Q, Q, Q];
array[Node] of var bool: nsa;
array[Edge] of var bool: esa;

array[3..4] of int: fb = array1d(3..4, [-2, -1]);
array[3..4] of int: tb = array1d(3..4, [-1, 0]);
array[-2..0] of var bool: nsb;
array[3..4] of var bool: esb;

array[1..0] of int: fc = [];
array[1..0] of int: tc = [];
array[1..2] of var bool: nsc;
array[1..0] of var bool: esc;

var bool: d2;
var bool: e1;

constraint nsa[Q] /\ not esa[PQ2];
constraint subgraph(fa, ta, nsa, esa);
constraint nsb[-1] /\ nsb[-2] = nsb[0];
constraint subgraph(fb, tb, nsb, esb);
constraint not nsc[1];
constraint subgraph(2, 0, fc, tc, nsc, esc);
constraint subgraph(3, 2, [1, 2], [2, 3], [true, d2, false], [e1, false]);

solve satisfy;

output ["ENUMSOL: \(nsa) \(esa) | \(nsb) \(esb) | \(nsc) | \(d2) \(e1)"];
