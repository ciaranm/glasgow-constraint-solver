High Priority TODO Items
========================

Code and Infrastructure
-----------------------

- Set up clang-format in a reasonable way.

- Switch to a modern build system.

- Run proof log tests automatically.

- Set up some kind of continuous integration.

- Factor out common test code.

Examples
--------

- Consistent command line handling.

- Do something about autotabulation in Skyscrapers.

Constraints
-----------

- What happens if a constraint is created entirely on constant variables?

- What happens if a variable appears multiple times in the same constraint?

- Test whether constraints achieve GAC.

State
-----

- The propagation queue is a filthy hack, and CNF propagation is slooooow.

- Tests and better code for State in general.

- Make State backtrackable or fast copyable.

- Change how IntegerSetVariable works so it is trivially copyable.

Design
------

- Can we isolate innards from user API?

- Linear constraints are a mess.

Proofs
------

- Proofs should make use of deletions and levels.

- Better comment names for constraints in the OPB files.

