include "globals.mzn";

% subgraph in the three contexts that are not a top-level constraint: reified,
% half-reified and negated, over nodes from 1, from 5 with edges from 0, and the
% six-argument spelling with a self loop. The builtin has no reified form, so
% each of these must reach the standard library's fzn_subgraph_reif
% decomposition rather than our redefinition (see "A reified call has to reach
% a reified decomposition" in dev_docs/minizinc.md); the guard is that the
% builtin never appears.
array[1..1] of int: f = [1];
array[1..1] of int: t = [2];
array[1..2] of var bool: ns;
array[1..1] of var bool: es;
var bool: b;

array[0..0] of int: f2 = array1d(0..0, [5]);
array[0..0] of int: t2 = array1d(0..0, [6]);
array[5..6] of var bool: ns2;
array[0..0] of var bool: es2;
var bool: c;

array[1..1] of var bool: ns3;
array[1..1] of var bool: es3;

constraint b <-> subgraph(f, t, ns, es);
constraint c -> subgraph(f2, t2, ns2, es2);
constraint not subgraph(1, 1, [1], [1], ns3, es3);

solve satisfy;

output ["ENUMSOL: \(b) \(ns) \(es) | \(c) \(ns2) \(es2) | \(ns3) \(es3)"];
