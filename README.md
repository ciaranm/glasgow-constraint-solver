The Glasgow Constraint Solver
=============================

This solver is a work in progress, with no stable API or design. The code that is here should mostly
work, but there is a lot missing.

Please contact [Ciaran McCreesh](mailto:ciaran.mccreesh@glasgow.ac.uk) with any queries.

.. contents

Getting Started
===============

This section describes how to build the solver, and how to create and solve a simple problem.

Compiling
---------

To build, you will need a C++20 compiler, such as GCC 10.3, as well as Boost (use
``libboost-all-dev`` on Ubuntu).

```shell
cmake -S . -B build
cmake --build build
```

If you have ``veripb`` installed (see below), you should then run


```shell
{ cd build ; ctest ; }
```

To generate API documentation, Doxygen must be installed. Then instead do:

```shell
cmake -S . -B build -DGCS_ENABLE_DOXYGEN=ON
cmake --build build
cmake --build build --target docs
```

By default, XCSP support will be enabled, which requires libxml2 (``libxml2-dev`` on Ubuntu) and
which will use Git to fetch an external dependency for parsing XCSP. To turn this off, do:

```shell
cmake -S . -B build -DGCS_ENABLE_XCSP=OFF
cmake --build build
```

Using the XCSP Solver
---------------------

To use the XCSP solver, run:

```shell
./build/xcsp_glasgow_constraint_solver instance.xml
```

Manually Solving a Constraint Optimisation Problem
--------------------------------------------------

Let's start by <a
href="https://www.minizinc.org/doc-2.5.5/en/modelling.html#an-arithmetic-optimisation-example">making
some cakes</a>. This example is a cut-down version of ``examples/cake/cake.cc``. We start by
including the header file and namespace,

```cpp
#include <gcs/gcs.hh>

using namespace gcs;
```

Now, we need a `Problem` instance. A constraint satisfaction problem consists of a number of
variables, each of which has a domain of possible values, together with a set of constraints which
must be satisfied. We can also have an objective variable, to maximise or minimise. Here, the
variables are the number of banana and chocolate cakes that we're going to bake, and their values
are between 0 and 100. (The ``0_i`` and ``100_i`` syntax turns a numeric literal into an `Integer`
instance, which is a simple wrapper class used for type safety.)

```cpp
Problem p;
auto banana = p.create_integer_variable(0_i, 100_i);
auto chocolate = p.create_integer_variable(0_i, 100_i);
```

Next, we need to define some constraints. For this example, all of our constraints are linear
inequalities.

```cpp
p.post(LinearLessEqual{Linear{{250_i, banana}, {200_i, chocolate}}, 4000_i});
p.post(LinearLessEqual{Linear{{2_i, banana}}, 6_i});
p.post(LinearLessEqual{Linear{{75_i, banana}, {150_i, chocolate}}, 2000_i});
p.post(LinearLessEqual{Linear{{100_i, banana}, {150_i, chocolate}}, 500_i});
p.post(LinearLessEqual{Linear{{75_i, chocolate}}, 500_i});
```

The first of these says that 250 times the number of banana cakes, plus 200 times the number of
chocolate cakes, is less than or equal to 4000. The remainder of these constraints impose further
similar restrictions.

Next, we need to define our profit variable, which we want to maximise because capitalism. If we get
400 moneys for each banana cake, and 450 moneys for each chocolate cake, we could say:

```cpp
auto profit = p.create_integer_variable(0_i, 107500_i, "profit");
p.post(LinearEquality{Linear{{400_i, banana}, {450_i, chocolate}, {-1_i, profit}}, 0_i});
p.maximise(profit);
```

Here the linear equality says that 400 times bananas plus 450 times chocolate equals profit.

We can now ask for a solution.

```cpp
solve(p, [&](const CurrentState & s) -> bool {
    cout << "banana cakes = " << s(banana) << ", chocolate cakes = "
         << s(chocolate) << ", profit = " << s(profit) << endl;
    return true;
});
```

The second argument here is a lambda, or callback function. It will be called every time the solver
finds a new candidate solution, and the last time it is called will be when an optimal solution has
been found. To get the actual value of a variable inside this callback, we use the ``s`` argument as
it it were a function. We return ``true`` from our callback to say that we want the solver to keep
going and try to find a better solution.

Finally, it is often a good idea to tell the solver which variables it should use for making
decisions. In this case, the banana and chocolate variables are our decision variables, so we could
instead use the ``solve_with`` function to specify a search strategy. The ``branch`` and
``guess`` parameters here can also be callbacks, but there are some common options available.

```cpp
solve_with(p,
    SolveCallbacks{
        .solution = [&](const CurrentState & s) -> bool {
            cout << "banana cakes = " << s(banana) << ", chocolate cakes = "
                 << s(chocolate) << ", profit = " << s(profit) << endl;
            return true;
        },
        .branch = branch_on_dom_then_deg(problem, vector<IntegerVariableID>{banana, chocolate}),
        .guess = guess_smallest_value_first()
    });
```

The ``examples/`` directory contains example programs that show how to use the solver as a program
author. It is probably best to start with ``examples/cake/cake.cc`` for a complete version of this
example, ``examples/crystal_maze/crystal_maze.cc`` and ``examples/sudoku/sudoku.cc`` for everyone's
favourite first two constraint programming problems, and ``examples/magic_square/magic_square.cc``
for some magic.

Proof Logging
-------------

The key feature of this solver is the ability to produce proof logs. Currently we are using the
VeriPB format. You can find out more here:

* VeriPB from https://github.com/StephanGocht/VeriPB/ .

To try out proof logging, run your favourite example program with the ``--prove`` command line
option. Or, for your own problem, pass an additional argument when creating your `Problem` object:

```cpp
Problem p{ProofOptions{"example.opb", "example.veripb"}};
```

This will produce a ``.opb`` file containing a low-level description of the model, as well as a
``.veripb`` file containing the associated proof. To verify the proof, use ``veripb example.opb
example.veripb``.

Navigating the Source Code
==========================

The ``gcs/`` directory contains the user-facing part of the API. The ``Problem`` class in
``gcs/problem.hh`` is your starting point, and you will want ``Problem::create_integer_variable``.
This returns an ``IntegerVariableID``, which is a light-weight handle which you can pass around by
value. For type-safety and avoiding overflow problems, the solver does not accept raw ``int`` and
similar types directly, and anywhere you use a numerical value you must create an ``Integer``.

You will also want some constraints. These can be found in the ``gcs/constraints/`` directory. Once
you construct a constraint, you can add it to a problem instance using ``Problem::post``.

Finally, you probably want to solve your problem. The ``solve`` function in ``gcs/solve.hh`` will do
this. It accepts a callback function as its second, which is called every time a solution is found.
The callback is given a ``CurrentState`` instance, and you can get a variable's value by using the
function call operator on the state.  If the callback function returns ``false``, no more solutions
will be found. If you are optimising something, via ``Problem::minimise``, this function will be
called every time a better incumbent is found, and ``true`` means "keep going and try to find
something better".

The contents of the ``gcs/innards/`` directory, and anything in the ``gcs::innards`` namespace, are
the solver's innards. These are probably not useful for end users, and if they are, they should
probably be turned into a cleaner API rather than exposed directly.

How Does the Solver Work Internally?
====================================

If we're looking to do as little as possible to get a working but not particularly efficient solver,
we probably need:

- integer variables
- a core set of constraints
- some kind of backtracking search
- some way sticking these things together

Variables
---------

There are two extremes on how to deal with variables, and various things in the middle. In a typical
SAT solver, variables are just integer indices, and the actual state of variables is held elsewhere
in the trail. Meanwhile, in a conventional OO style constraint solver, a variable is a class that
holds a set of values. I'm becoming increasingly unfond of the OO style, for at least four reasons:

- It puts state in awkward places. Is the variable you create when you define your model the same as
  the variable you get when you've found a solution? Can you just read its value, or do you have to
  mess around with it? Every solution I've seen to this is ugly in some way.

- What about multi-threading, etc?

- It makes having lots of variables expensive. If something simple like a binary variable involves
  multiple memory allocations, performance is terrible compared to a SAT solver.

- It gives us object lifetime issues. Think Sudoku, and how every variable appears in several all
  different constraints: this means variables need to be references rather than raw objects. But
  then also think temporaries, used in arithmetic expressions, etc. Where do they live? Who is
  responsible for the variable object's lifetime?

On the other hand, treating everything as a binary variable, like in a SAT solver, means awful
blowups on large domains. So, whilst I like the idea of variables just being identifiers that,
behind the scenes, index into a state data structure, it's worth thinking carefully about how we
store this state. The solution I'm going with for now is:

- We have a Problem object, which does bookkeeping.

- From a user perspective, variables are IDs, which are an opaque, lightweight thing you can copy
  around etc. We can create new ones as needed via our problem object. Also, we can create 'fake'
  variables corresponding to integer constants in an easy way, because this is convenient, and avoids
  having to overload constraints.

- Whenever we've found a solution, we're given a temporary reference to a State object, that can
  be queried using a variable identifier to get its value. (Actually, we get a CurrentState, which
  avoids exposing all sorts of ugly innards.)

Then there's the question of how variable state is stored. A variable is a set of values, but a set
is a horribly inefficient data structure that is expensive to copy, and involves all kinds of
unpleasant memory allocation and dereferencing. If we knew that variables only ever store ranges,
we could just store bounds, or if we knew variables were small, we could use a fixed size bitset
for its domain, but both of these solutions lack generality. So how do we get all of the nice
things?

If we can abstract away all the places that actually directly play around with a variable's values
directly, there's nothing stopping us from using algebraic types behind the scenes to store a
variable's state as either a constant, or a range, or a compact bitset, or an ugly big set if it's
really necessary. For constraints, it looks like it suffices to support a small list of query
operations for each variable:

- How many values are in the domain?
- What is the lower / upper bound?
- Is this value in the domain?
- Iterate over each value in the domain in order.

And for the public user interface, we might only need a single common operation:

- Give me the single value in this domain, or exception if it doesn't have a unique value.

To modify state, we seem to need:

- This variable takes exactly this value.
- This variable does not take this value.
- This variable is at least / at most this value.

Whilst there's a bit of complexity in dealing with each of these operations and with all of the
things it might do to the different ways a value set might be represented, we can put this code in
exactly one place. An additional advantage of keeping all this together is for tracking state
changes, for watches etc: three constraints might each think they're eliminating an arbitrary value
from a domain, but we can spot that together they've just done a bounds change. I expect this will
be similarly useful for proof logging.

Constraints
-----------

Constraints are user-facing. Each constraint is associated with zero or more propagators, which do
the actual work. A propagator is always called at least once, at the root node. After that, it is
only called when triggered by an event. Events include a specific variable being instantiated, a
specific variable having its bounds changed, and a specific variable having any of its values
deleted. (Instantiated implies both other kinds of events, and bounds implies any values, so
multiple triggers are not needed.) A propagator is then called, and it can make some inferences. It
must then return information on whether or not it actually changed anything, and whether or not it
should be called again in the future. The easiest constraints to understand are probably
``NotEquals`` and ``Table`` (the latter of which uses ``propagate_extensional`` to do the hard work,
because this code is used by other constraints too).

For proof logging, every constraint must also be able to describe itself in low level terms. Usually
this is done via members of the ``Propagators`` class such as ``define_cnf``,
``define_at_most_one``, ``define_linear_le``, ``define_linear_eq`` and ``define_pseudoboolean_ge``.
This should only be done if ``Propagators::want_nonpropagating()`` is true.

Any inference that is carried out, via ``State::infer``, must also be justified for proof logging.
This can be done by passing a ``NoJustificationNeeded`` or ``JustifyUsingRUP`` instance, for simple
constraints, but complex reasoning will require a ``JustifyExplicitly`` instance which includes a
callback to create the relevant proof steps.

If the compiler macro ``GCS_TRACK_ALL_PROPAGATIONS`` is defined, the proof log will include explicit
origin statements for every ``JustifyUsingRUP`` propagation, which may be helpful in debugging bad
proofs. It will also slow things down considerably.

Backtracking Search
-------------------

For now, this is boring. In the future, we'll probably do something like Solution-Biased search.

How Do We Know It's Correct?
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

Acknowledgements
================

This work is supported by a Royal Academy of Engineering Research Fellowship. Part of this work was
done while the author was participating in a program at the Simons Institute for the Theory of
Computing.

<!-- vim: set tw=100 spell spelllang=en : -->

