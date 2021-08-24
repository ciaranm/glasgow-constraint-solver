How do we know it's correct?
============================

We have a problem, we run the solver, we get an answer. Why should we believe it's correct? For
satisfiable decision instances this isn't such a problem (although it's not trivial either), but for
unsatisfiable decision instances and for optimisation problems, we know that some solvers are, uh,
not entirely accurate all of the time. Unfortunately, conventional testing seems to be at best
minimally effective in establishing solver correctness, and correct-by-construction formal methods
seem to be far too expensive to work even for naive implementations of simple constraints like
all-different. The approach we take here is proof logging. The idea is as follows:

- The solver converts the high level constraint problem given into a low-level pseudo-Boolean
  model, written out in the standard OPB format (by default, using an extension that allows for
  flexible variable names).

- If the instance is satisfiable, the solver gives a witness, in the corresponding pseudo-Boolean
  form. If the instance is unsatisfiable, we provide a proof in VeriPB format that the
  pseudo-Boolean instance is unsatisfiable. For optimality and finding all solutions, we effectively
  do both (the VeriPB format knows about optimisation and enumeration).

- The user can then feed the OPB file and the VeriPB proof file to the VeriPB checker, which
  verifies that the supplied proof is valid.

So, this reduces the problem of trusting the solver down to two smaller problems: believing that the
OPB file we produce is actually representative of the high level constraint model, and trusting the
VeriPB checker. The latter we take on faith, although the VeriPB format is intentionally simple
enough that you should probably be able to write your own proof checker if you prefer.

Encoding high level constraints in OPB format is mostly almost straightforward, because we
deliberately use a very simple encoding, and derive any additional constraints or inference in a way
that is proof-checked. The main problem is all the awful special edge cases: whilst you might think
it is easy to explain what the constraint "(x < y) <-> z" does, this gets to be moderately fiddly
when x and y have different and potentially non-overlapping domains. So, for each constraint, we
test that it is defined correctly over a range of hand-crafted and randomly generated sequences of
variables: we enumerate all solutions to the problem that has just that constraint, and compare
them to a computer-generated list of all solutions that is created just using a piece of
solution-checking code. This means that, if we believe we can write a function that checks whether
"(x < y) <-> z" holds given ints x and y and a boolean z, then we can believe we have defined the
constraint correctly, at least for the choices of test input. We then also run the VeriPB proof
checker on the "find all solutions" search tree, to check that the OPB definition is consistent.

This isn't perfect, though: it assumes we can generate a good set of test variable domains. It also
doesn't check edge cases that we haven't thought of, like "what if x and y are the same variable?",
or "what if z is defined as a literal that mentions x?".

Finally, we also use this setup to test that a constraint achieves GAC (assuming it is supposed to):
during every step of the backtracking search, we also check that every remaining value has a
support. This isn't particularly fast, but it's not so slow that it's prohibitive to do it as part
of a normal automated test run.

<!-- vim: set tw=100 spell spelllang=en : -->
