include "globals.mzn";

% connected and dconnected have no override of their own: the standard library
% gives them a root over index_set(ns) and calls reachable or dreachable, which
% reach ours (#1006). So the shapes here are the node and edge index sets that
% root inherits: connected over nodes from -3 and edges from 0, connected over a
% one-node enum with an empty enum of edges, and dconnected over nodes from 10
% and edges from -1, with a 2-cycle and a self loop.
array[0..2] of int: fe = array1d(0..2, [-3, -2, -3]);
array[0..2] of int: te = array1d(0..2, [-2, -1, -1]);
array[-3..-1] of var bool: nse;
array[0..2] of var bool: ese;

enum Solo = {Only};
enum NoEdge = {};
array[NoEdge] of Solo: ff = [];
array[NoEdge] of Solo: tf = [];
array[Solo] of var bool: nsf;
array[NoEdge] of var bool: esf;

array[-1..2] of int: fg = array1d(-1..2, [10, 11, 11, 12]);
array[-1..2] of int: tg = array1d(-1..2, [11, 10, 11, 10]);
array[10..12] of var bool: nsg;
array[-1..2] of var bool: esg;

constraint nse[-3];
constraint connected(fe, te, nse, ese);
constraint connected(ff, tf, nsf, esf);
constraint dconnected(fg, tg, nsg, esg);

solve satisfy;

output ["ENUMSOL: \(nse) \(ese) | \(nsf) | \(nsg) \(esg)"];
