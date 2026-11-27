include "globals.mzn";

% Shapes of tree that the redefinitions shift (#1006): fzn_tree_enum.mzn
% subtracts min(index_set(ns)) from the endpoints and the root, and
% fzn_tree_int.mzn subtracts 1. Here: enum nodes and edges round a triangle,
% with one edge forced in and the root over the enum; nodes from -2 and edges
% from 4, with a pair of parallel edges equated (so the builtin sees one
% variable twice, and neither can be used), a self loop, and a root whose
% domain reaches past the nodes on both sides; the N-and-E spelling over a
% single node with no edges; and steiner, which reaches the builtin through the
% standard library's wrapper and the N-and-E spelling, with its weight a
% variable rather than an objective.
enum Node = {P, Q, R};
enum Edge = {PQ, QR, RP};
array[Edge] of Node: fa = [P, Q, R];
array[Edge] of Node: ta = [Q, R, P];
array[Node] of var bool: nsa;
array[Edge] of var bool: esa;
var Node: ra;

array[4..7] of int: fb = array1d(4..7, [-2, -2, -1, -1]);
array[4..7] of int: tb = array1d(4..7, [-1, -1, -1, 0]);
array[-2..0] of var bool: nsb;
array[4..7] of var bool: esb;
var -6..6: rb;

array[1..0] of int: fc = [];
array[1..0] of int: tc = [];
array[1..1] of var bool: nsc;
array[1..0] of var bool: esc;

array[1..3] of int: fd = [1, 2, 1];
array[1..3] of int: td = [2, 3, 3];
array[1..3] of int: wd = [1, 2, 4];
array[1..3] of var bool: nsd;
array[1..3] of var bool: esd;
var int: Kd;

constraint nsa[P] /\ ra != R /\ esa[RP];
constraint tree(fa, ta, ra, nsa, esa);
constraint nsb[0] /\ esb[4] = esb[5];
constraint tree(fb, tb, rb, nsb, esb);
constraint tree(1, 0, fc, tc, 1, nsc, esc);
constraint nsd[1] /\ nsd[3];
constraint steiner(3, 3, fd, td, wd, nsd, esd, Kd);

solve satisfy;

output ["ENUMSOL: \(ra) \(nsa) \(esa) | \(rb) \(nsb) \(esb) | \(nsc) | \(nsd) \(esd) \(Kd)"];
