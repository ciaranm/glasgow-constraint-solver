include "globals.mzn";

% Shapes of path that the redefinitions shift (#1006): fzn_path_enum.mzn
% subtracts min(index_set(ns)) from the endpoints, the source and the target,
% and fzn_path_int.mzn subtracts 1. The enum spelling's edges may be indexed
% from anywhere. Here: enum nodes round a triangle with edges from 0, a pair of
% parallel edges, a self loop, a fixed source and a variable target; nodes from -2, a source and target whose domains reach past the nodes
% on both sides and may be equal, and two edge variables equated (so the
% builtin sees one variable twice); the N-and-E spelling with the source fixed
% at the far end; and bounded_path, which reaches the builtin through the
% standard library's wrapper, over nodes from 7 and edges from -1, with its
% weight a variable rather than an objective.
enum Stop = {A, B, C};
array[0..4] of Stop: fa = array1d(0..4, [A, A, B, B, C]);
array[0..4] of Stop: ta = array1d(0..4, [B, B, C, B, A]);
array[Stop] of var bool: nsa;
array[0..4] of var bool: esa;
var Stop: tA;

array[1..3] of int: fb = [-2, -1, -2];
array[1..3] of int: tb = [-1, 0, 0];
array[-2..0] of var bool: nsb;
array[1..3] of var bool: esb;
var -5..5: sb;
var -5..5: tB;

array[1..2] of int: fc = [1, 2];
array[1..2] of int: tc = [2, 3];
array[1..3] of var bool: nsc;
array[1..2] of var bool: esc;
var 1..3: tC;

array[-1..1] of int: fd = array1d(-1..1, [7, 8, 7]);
array[-1..1] of int: td = array1d(-1..1, [8, 9, 9]);
array[-1..1] of int: wd = array1d(-1..1, [2, 3, 7]);
array[7..9] of var bool: nsd;
array[-1..1] of var bool: esd;
var int: Kd;

constraint path(fa, ta, A, tA, nsa, esa);
constraint sb != -2 /\ nsb[0] /\ esb[1] = esb[2];
constraint path(fb, tb, sb, tB, nsb, esb);
constraint path(3, 2, fc, tc, 3, tC, nsc, esc);
constraint bounded_path(fd, td, wd, 7, 9, nsd, esd, Kd);

solve satisfy;

output ["ENUMSOL: \(tA) \(nsa) \(esa) | \(sb) \(tB) \(nsb) \(esb) | \(tC) \(nsc) \(esc) | \(nsd) \(esd) \(Kd)"];
