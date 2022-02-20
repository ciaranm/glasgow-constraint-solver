High Priority TODO Items
========================

Code and Infrastructure
-----------------------

- Go through <a href="TOOLING.md">TOOLING.md</a> and see if any of this is fixable.

- Get an include what you use tool, and possibly a using what you use tool, set up.

- Figure out linting.

- Switch to a modern build system.

- Run proof log tests automatically.

- Set up some kind of continuous integration.

- Factor out common test code.

- Replace for\_each\_with\_index with C++20 stuff so we can use break in loops.

Examples
--------

- Do something about autotabulation in Skyscrapers.

Constraints
-----------

- What happens if a constraint is created entirely on constant variables?

- What happens if a variable appears multiple times in the same constraint?

- What if it appears multiple times, but involving views?

- Test whether constraints achieve GAC, and tidy up existing tests that do this
  to use common code.

- Random branching order and hole poking in tests.

- Circuit, so we can do all the MiniCP benchmarks.

State
-----

- The propagation queue is a filthy hack.

- Tests and better code for State in general.

- Make State backtrackable or fast copyable.

- Change how IntegerSetVariable works so it is trivially copyable.

- Consider a range set of some kind.

- Template out some of the variable representations so we don't pay the price
  for offsets etc if we aren't using them.

- Fast way of unioning and intersecting many domains.

Design
------

- Can we isolate innards from user API?

- Have a think about removing Boolean variables, and just using literals
  everywhere instead. Might not be very useful if we need to introduce float
  and set variables for MiniZinc, though.

- Can we have an IntegerViewOfLiteral value? Or does this lead to nasty
  recursion issues? Either way, being able to use reified values directly
  in linear and extensional constraints might be interesting.

- Go through everywhere that uses Integer::raw\_value and see if it should
  use something else instead.

- Some way of handling limits, ctrl+c, etc.

Proofs
------

- Better comment names for constraints in the OPB files.

- A way to handle variables with large domains.

- Don't generate binary encoding for 0/1 variables.

