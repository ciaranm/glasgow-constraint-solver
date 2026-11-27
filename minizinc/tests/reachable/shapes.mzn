include "globals.mzn";

% Shapes of reachable that the redefinitions shift (#1006). Nodes are
% index_set(ns), and the endpoints and the root are in that numbering, so
% fzn_reachable_enum.mzn subtracts min(index_set(ns)) from all three and
% fzn_reachable_int.mzn subtracts 1. Here: enum nodes and enum edges with a
% fixed root; nodes from -2 and edges from 5, with a self loop, a pair of
% parallel edges, two node variables equated (so the builtin sees one variable
% twice) and a root whose domain reaches past the nodes on both sides; the
% N-and-E spelling with no edges and a root domain wider than 1..N; a single
% node at 100 with no edges; and the N-and-E spelling again with Boolean
% literals among the node and edge variables.
enum Node = {P, Q, R};
enum Edge = {PQ, QR};
array[Edge] of Node: fa = [P, Q];
array[Edge] of Node: ta = [Q, R];
array[Node] of var bool: nsa;
array[Edge] of var bool: esa;

array[5..8] of int: fb = array1d(5..8, [-2, -1, -1, 0]);
array[5..8] of int: tb = array1d(5..8, [-1, -1, 0, -1]);
array[-2..0] of var bool: nsb;
array[5..8] of var bool: esb;
var -5..5: rb;

array[1..0] of int: fc = [];
array[1..0] of int: tc = [];
array[1..2] of var bool: nsc;
array[1..0] of var bool: esc;
var 0..3: rc;

array[1..0] of int: fd = [];
array[1..0] of int: td = [];
array[100..100] of var bool: nsd;
array[1..0] of var bool: esd;
var 99..101: rd;

var bool: n2;
var bool: e1;

constraint reachable(fa, ta, Q, nsa, esa);
constraint rb != -2 /\ nsb[-2] = nsb[0];
constraint reachable(fb, tb, rb, nsb, esb);
constraint reachable(2, 0, fc, tc, rc, nsc, esc);
constraint reachable(fd, td, rd, nsd, esd);
constraint reachable(3, 2, [1, 2], [2, 3], 1, [true, n2, false], [e1, false]);

solve satisfy;

output ["ENUMSOL: \(nsa) \(esa) | \(rb) \(nsb) \(esb) | \(rc) \(nsc) | \(rd) \(nsd) | \(n2) \(e1)"];
