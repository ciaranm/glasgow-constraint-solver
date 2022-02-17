Examples, and Navigating the Source Code
========================================

The ``examples/`` directory contains example programs that show how to use the solver as a program
author. It is probably best to start with ``examples/cake/cake.cc`` for some delicious cakes,
``examples/crystal_maze/crystal_maze.cc`` for everyone's favourite first constraint programming
problem, and ``examples/magic_square/magic_square.cc`` for some magic.

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

The contents of the ``gcs/detail/`` directory, and anything in the ``gcs::detail`` namespace, are
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
this is done via members of the ``Propagators`` class such as ``cnf``, ``at_most_one``, and
``sanitised_linear_le``. This is only done if ``Propagators::want_nonpropagating()`` is true.

Any inference that is carried out, via ``State::infer``, must also be justified for proof logging.
This can be done by passing a ``NoJustificationNeeded`` or ``JustifyUsingRUP`` instance, for simple
constraints, but complex reasoning will require a ``JustifyExplicitly`` instance which includes a
callback to create the relevant proof steps.

Backtracking Search
-------------------

For now, this is boring. In the future, we'll probably do something like Solution-Biased search.

Sticking it Together
--------------------

See the examples.

<!-- vim: set tw=100 spell spelllang=en : -->
