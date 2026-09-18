See Laurent D. Michel, Pierre Schaus, Pascal Van Hentenryck: "MiniCP: a
lightweight solver for constraint programming". Math. Program. Comput. 13(1):
133-184 (2021).

These programs are meant to reproduce MiniCP's search trees exactly, so their
models, their default search, and the default propagation strength of every
constraint they post must not change (`qap`'s commented-out `AllDifferent`
is deliberate, for example). That includes changes made elsewhere: altering
the default consistency or algorithm of a constraint used here changes the
search tree too. The ctest lanes cannot catch this. They run small instances
(and none for `tsp`) and check only for correct answers and verified proofs,
which a stronger or weaker propagator still produces. To check by hand,
compare the `recursions:` line against the count that `magic_series`,
`magic_square` and `n_queens` print ("This should take N recursions with
default options"). `qap` and `tsp` print no such count, so compare them
against `main` instead.
