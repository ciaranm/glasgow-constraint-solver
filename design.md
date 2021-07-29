What do we actually need to make a solver?
------------------------------------------

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

- We have a problem object, which does bookkeeping.

- From a user perspective, variables are IDs, which are an opaque, lightweight thing you can copy
  around etc. We can create new ones as needed via our problem object. Also, we can create 'fake'
  variables corresponding to integer constants in an easy way, because this is convenient, and avoids
  having to overload constraints.

- Whenever we've found a solution, we're given a temporary reference to a state object, that can
  be queried using a variable identifier to get its value.

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

The minimal set of constraints needed to work with MiniZinc is approximately:

- element, minimum, maximum
- abs, plus, times, div, mod, power
- boolean and, or, cnf
- reified equals and less-equals
- reified integer linear equalities and inequalities

And realistically we probably want to do some of the globals:

- alldifferent
- count
- nvalue
- lex, precede chain, increasing, etc

But do we really need to write propagators for all of these? CNF is great, we can propagate it in
sub-linear(ish) time. Why not compile everything down to CNF? This also means we don't need to worry
about propagation efficiency and memory for millions of constraints.

The problem, of course, is that CNF encodings for some of these constraints are either large or
don't propagate. But what if we mostly use CNF where we can? And when that doesn't work, compile to
either linear inequalities or table constraints? And only when all else fails, have actual serious
propagators to do things like Hall sets?  This means we can focus on writing really fast propagators
for, say, CNF, table, and linear equalities, and not worry so much about the rest. It also means we
can do things like conflict analysis on the CNF, and linear relaxations, and merging tables.

Note that because we're not a SAT solver, compiling to CNF doesn't require an explicit boolean
variable for each CP variable-value. We can just have literals refer to CP variable-values, and
sort things out inside the CNF propagator. This also lets us have multiple virtual encodings for
each CP variable without paying the cost of explicitly creating them, so we can have literals
that mean "x < 3" and "x = 3".

From a user perspective, they don't really need to see this. They can create and post constraints
however they like. A constraint is just a temporary, short-lived thing that compiles itself into one
or more of a small number of low-level representations, and possibly installs a full propagation
routine if it's really needed.

I expect that eventually, we'll end up with full propagation for quite a few constraints, but
compiling most things down seems to be an easy way of getting started. For example, all of the
arithmetic constraints can be brute-forced into table constraints in only a few lines of code, and
we get fairly fast propagators with watches for free (at the slight expense of encoding size).

Backtracking Search
-------------------

For now, this is boring.

Sticking it Together
--------------------

See the examples.

<!-- vim: set tw=100 spell spelllang=en : -->
