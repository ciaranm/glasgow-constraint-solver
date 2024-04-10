% Simple nurse rostering
include "regular.mzn";
int: num_nurses = 7;
set of int: NURSES = 1..num_nurses;
int: num_days = 10;
set of int: DAYS = 1..num_days;
int: req_day = 3;
int: req_night = 2;
int: min_night = 2;
int: S = 3;
set of int: SHIFTS = 1..S;
int: d = 1; int: n = 2; int: o = 3;
array[SHIFTS] of string: name = ["d","n","-"];
int: Q = 6; int: q0 = 1; set of int: STATES = 1..Q;
array[STATES,SHIFTS] of int: t =
[| 2, 3, 1 % state 1
| 4, 4, 1 % state 2
| 4, 5, 1 % state 3
| 6, 6, 1 % state 4
| 6, 0, 1 % state 5
| 0, 0, 1|]; % state 6
array[NURSES,DAYS] of var SHIFTS: roster;
constraint forall(j in DAYS)(
sum(i in NURSES)(bool2int(roster[i,j] == d)) == req_day /\
sum(i in NURSES)(bool2int(roster[i,j] == n)) == req_night
);
constraint forall(i in NURSES)(
regular([roster[i,j] | j in DAYS], Q, S, t, q0, STATES) /\
sum(j in DAYS)(bool2int(roster[i,j] == n)) >= min_night
);
solve satisfy;
output [ name[fix(roster[i,j])]
++ if j==num_days then "\n" else " " endif
| i in NURSES, j in DAYS ];