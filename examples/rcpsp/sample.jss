 instance sample4x4
+++++++++++++++++++++++++++++
A hand-written four-job, four-machine job shop, in the standard OR-Library
layout that the ft, la, abz, orb, swv and ta sets are distributed in. Written
here rather than taken from a benchmark set, so it is small enough to prove
quickly and there is no licence question about redistributing it.

The optimum is 23, and neither kind of reasoning reaches it alone: the busiest
machine (machine 0) carries 19 units of work and the longest job (job 3) is 17
long, so both of the easy bounds are slack and the machines and the chains have
to be reasoned about together.

Chosen to be discriminating rather than merely valid. Every unary rule changes
the search on it, and by different amounts, so a rule that silently stopped
inferring would show up here: against 164 recursions with none of them on,
--disjunctive-edge-finding gives 125, --disjunctive-not-first-not-last 144,
--disjunctive-overload 132 and --disjunctive-detectable-precedences-set 125.

This blurb is also the reader's test that it skips a header: the bundled
jobshop1.txt puts an `instance` line and a description between rows of plus
signs, and everything down to the dimensions line has to be ignored.
+++++++++++++++++++++++++++++
 4 4
 2 2  1 3  0 5  3 2
 1 5  0 5  2 3  3 3
 0 4  1 1  2 1  3 6
 2 5  0 5  1 2  3 5
