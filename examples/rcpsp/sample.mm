A hand-written multi-mode RCPSP instance in the PSPLIB .mm format, for the --mm
reader. Written here rather than taken from a benchmark set, so it is small
enough to prove quickly and there is no licence question about redistributing
it. Everything above the first row of stars is ignored by the reader, which
finds each section by its heading.

Five real activities between a dummy source and sink, each with three modes,
two resources that are capped at every time point and one budget spent over the
whole project.

Chosen to be discriminating rather than merely valid, on the two things that
make this format worth reading at all:

  * A mode fixes both a duration and the demands that go with it, so the
    trade-off is real. The optimum is 10 against a critical path of 5, so the
    resources decide the answer and not the chains.

  * The budget binds, and hard. Raise the 15 on the last line to 22 and the
    optimum drops from 10 to 6: four of the ten time units are there because
    the cheap modes cannot all be afforded together. Without that, every
    activity would take its shortest mode and this would be a plain RCPSP with
    extra steps.

Every energetic rule that reads a variable length or height changes the search
on it --- 109 recursions with none of them, 107 with edge-finding, with the
time-table and energetic strengthenings, and with not-first / not-last --- so a
rule that stopped reasoning about variable arguments would show up here.
************************************************************************
file with basedata            : sample.bas
initial value random generator: 0
************************************************************************
projects                      :  1
jobs (incl. supersource/sink ):  7
horizon                       :  0
RESOURCES
  - renewable                 :  2   R
  - nonrenewable              :  1   N
  - doubly constrained        :  0   D
************************************************************************
PROJECT INFORMATION:
pronr.  #jobs rel.date duedate tardcost  MPM-Time
    1     5      0       0        0       0
************************************************************************
PRECEDENCE RELATIONS:
jobnr.    #modes  #successors   successors
    1        1        2        2  3
    2        3        3        3  5  6
    3        3        2        4  6
    4        3        1        6
    5        3        1        6
    6        3        1        7
    7        1        0        
************************************************************************
REQUESTS/DURATIONS:
jobnr. mode duration  R 1  R 2  N 1
------------------------------------------------------------------------
    1      1       0     0    0     0
    2      1       2     5    1     5
           2       4     5    5     2
           3       5     0    1     3
    3      1       1     6    3     2
           2       5     0    4     4
           3       5     5    2     1
    4      1       1     6    0     6
           2       4     5    2     6
           3       4     2    5     3
    5      1       2     2    2     4
           2       2     0    4     5
           3       3     0    4     6
    6      1       1     0    5     2
           2       2     4    2     1
           3       3     2    3     2
    7      1       0     0    0     0
************************************************************************
RESOURCEAVAILABILITIES:
  R 1  R 2  N 1
    6    5   15
************************************************************************
