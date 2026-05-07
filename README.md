The Glasgow Constraint Solver
=============================

This solver is a work in progress, with no stable API or design. The code that is here should mostly
work, but there is a lot missing.

Please contact [Ciaran McCreesh](mailto:ciaran.mccreesh@glasgow.ac.uk) with any queries.

Contents
========

- [Getting Started](#getting-started)
  * [Compiling](#compiling)
  * [Using the XCSP Solver](#using-the-xcsp-solver)
  * [Manually Solving a Constraint Optimisation Problem](#manually-solving-a-constraint-optimisation-problem)
  * [Proof Logging](#proof-logging)
- [Navigating the Source Code](#navigating-the-source-code)
- [Developer Documentation](#developer-documentation)
- [How Do We Know It's Correct?](#how-do-we-know-its-correct)
- [Acknowledgements](#acknowledgements)

Getting Started
===============

This section describes how to build the solver, and how to create and solve a simple problem.

Compiling
---------

### Dependencies

**Required:**
- A C++23 compiler. GCC 13 (Ubuntu 24.04) is the oldest tested; GCC 15 and Clang 21
  are the primary development compilers. Clang on macOS uses libc++ rather than
  libstdc++, which affects which C++23 features are available natively.
- CMake 3.21 or later.

**Fetched automatically by CMake** (no manual installation needed):
- [Catch2](https://github.com/catchorg/Catch2) — test framework (tests only)
- [cxxopts](https://github.com/jarro2783/cxxopts) — command-line parsing (examples and
  MiniZinc frontend only)
- [nlohmann/json](https://github.com/nlohmann/json) — JSON parsing (MiniZinc support only)
- [fmt](https://github.com/fmtlib/fmt) — string formatting, fetched only when the
  compiler's standard library lacks ``<format>`` (e.g. Clang with libc++ on macOS)
- A ``<generator>`` polyfill, fetched only when the compiler's standard library lacks
  ``std::generator`` (e.g. Clang with libc++ on macOS)
- [gch::small_vector](https://github.com/gharveymn/small_vector) — small-buffer-optimised
  vector container, used internally for variable domain storage

**Optional external tools:**
- [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) — proof checker, required
  to run the full test suite. Written in Rust; install with ``cargo install --path .``
  after cloning.
- libxml2 — required for XCSP support (``libxml2-dev`` on Ubuntu, ``libxml2`` via Brew).
  XCSP support can be disabled with ``-DGCS_ENABLE_XCSP=OFF``.
- [MiniZinc](https://www.minizinc.org) — required to use the MiniZinc frontend
  (``minizincide`` via Brew on macOS). The frontend can be disabled with
  ``-DGCS_ENABLE_MINIZINC=OFF``.
- [Doxygen](https://www.doxygen.nl) — required to generate API documentation.

### Build types

Three build types are supported, selected via `CMAKE_BUILD_TYPE`. The easiest way to use
them is through the named presets in `CMakePresets.json`:

```shell
cmake --preset release  && cmake --build --preset release  --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)  # optimised, -march=native
cmake --preset debug    && cmake --build --preset debug    --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)  # -O0, full debug info
cmake --preset sanitize && cmake --build --preset sanitize --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)  # AddressSanitizer + UBSan
```

Each preset configures its own build directory (`build/`, `build-debug/`,
`build-sanitize/`), so all three can coexist on disk.

If you prefer not to use presets, the release build is just:

```shell
cmake -S . -B build
cmake --build build --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)
```

The sanitize build runs the code under [AddressSanitizer](https://clang.llvm.org/docs/AddressSanitizer.html)
and [UndefinedBehaviourSanitizer](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html),
which catch memory errors and undefined behaviour at runtime. It is roughly 2× slower than
release and is run automatically on every check-in.

### Running the tests

If you have ``veripb`` installed (see below), run the tests with:

```shell
ctest --preset release          # using presets
{ cd build ; ctest ; }          # without presets
```

For a sanitizer test run, set the following environment variables so that the first error
halts the process with a useful backtrace rather than continuing:

```shell
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
UBSAN_OPTIONS=halt_on_error=1:print_stacktrace=1 \
ctest --preset sanitize
```

### Optional features

XCSP and MiniZinc support are enabled by default but can be turned off to reduce
build dependencies (see the Dependencies section above for what each requires):

```shell
cmake -S . -B build -DGCS_ENABLE_XCSP=OFF -DGCS_ENABLE_MINIZINC=OFF
cmake --build build --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)
```

Note that both frontends are currently extremely minimal and do not support most
constraints or language features.

To generate API documentation with Doxygen:

```shell
cmake -S . -B build -DGCS_ENABLE_DOXYGEN=ON
cmake --build build --parallel $(nproc 2>/dev/null || sysctl -n hw.logicalcpu)
cmake --build build --target docs
```

Using the XCSP Solver
---------------------

To use the XCSP solver, run:

```shell
./build/xcsp_glasgow_constraint_solver instance.xml
```

Using the MiniZinc Solver
-------------------------

The easiest way is probably to add symbolic links into your user solver directory, which you can
find by running `minizinc --config-dirs` and looking for `userSolverConfigDir`. For example:

```shell
ln -s $HOME/glasgow-constraint-solver/minizinc $HOME/.minizinc/solvers/glasgow
ln -s $HOME/glasgow-constraint-solver/minizinc/glasgow.msc $HOME/.minizinc/solvers/glasgow.msc
```

Then you can run

```shell
minizinc --solver glasgow -a -s cake.mzn
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
p.post(WeightedSum{} + 250_i * banana + 200_i * chocolate <= 4000_i);
p.post(WeightedSum{} + 2_i * banana <= 6_i);
p.post(WeightedSum{} + 75_i * banana + 150_i * chocolate <= 2000_i);
p.post(WeightedSum{} + 100_i * banana + 150_i * chocolate <= 500_i);
p.post(WeightedSum{} + 75_i * chocolate <= 500_i);
```

The first of these says that 250 times the number of banana cakes, plus 200 times the number of
chocolate cakes, is less than or equal to 4000. The remainder of these constraints impose further
similar restrictions. Here we are making use of some convenience overloads; we could also be more
verbose, and have written these constraints like:

```cpp
p.post(LinearLessEqual{WeightedSum{{{250_i, banana}, {200_i, chocolate}}}, 4000_i});
```

Next, we need to define our profit variable, which we want to maximise because capitalism. If we get
400 moneys for each banana cake, and 450 moneys for each chocolate cake, we could say:

```cpp
auto profit = p.create_integer_variable(0_i, 107500_i, "profit");
p.post(WeightedSum{} + 400_i * banana + 450_i * chocolate == 1_i * profit);
p.maximise(profit);
```

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
if it were a function. We return ``true`` from our callback to say that we want the solver to keep
going and try to find a better solution.

Finally, it is often a good idea to tell the solver which variables it should use for making
decisions. In this case, the banana and chocolate variables are our decision variables, so we could
instead use the ``solve_with`` function to specify a search strategy. The ``branch``
parameter here can also be a callback, but there are some common options available using the
``branch_with`` function, and the functions in the ``gcs::variable_order::`` and
``gcs::value_order::`` namespaces.

```cpp
solve_with(p,
    SolveCallbacks{
        .solution = [&](const CurrentState & s) -> bool {
            cout << "banana cakes = " << s(banana) << ", chocolate cakes = "
                 << s(chocolate) << ", profit = " << s(profit) << endl;
            return true;
        },
        .branch = branch_with(
            variable_order::dom_then_deg(vector<IntegerVariableID>{banana, chocolate}),
            value_order::largest_first())
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
VeriPB 3.0 format. You can find out more here:

* VeriPB from https://gitlab.com/MIAOresearch/software/VeriPB

VeriPB is now written in Rust and can be installed via the default Rust build tool `cargo`. 
After cloning the repository:
```bash
cd ./VeriPB
cargo install --path .
```
To try out proof logging, run your favourite example program with the ``--prove`` command line
option. Or, for your own problem, pass an additional argument to ``solve()`` or ``solve_with()``:

```cpp
solve_with(p,
    SolveCallbacks{
        .solution = [&](const CurrentState & s) -> bool {
            cout << "banana cakes = " << s(banana) << ", chocolate cakes = "
                 << s(chocolate) << ", profit = " << s(profit) << endl;
            return true;
        },
        .branch = branch_with(
            variable_order::dom_then_deg(vector<IntegerVariableID>{banana, chocolate}),
            value_order::largest_first())
    },
    make_optional<ProofOptions>("cake"));
```

This will produce a ``cake.opb`` file containing a low-level description of the model, as well as a
``cake.pbp`` file containing the associated proof. To verify the proof, use ``veripb cake.opb
cake.pbp``.

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

Developer Documentation
=======================

In-depth notes on individual subsystems live in the ``dev_docs/`` directory. These are aimed at
developers (human or AI) working on the solver itself, not at end users. See ``dev_docs/README.md``
for an index.

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

For how each constraint produces its OPB encoding and how we test that the encoding matches the
constraint's semantics, see the [developer documentation](dev_docs/).

Acknowledgements
================

This work is supported by a Royal Academy of Engineering Research Fellowship. Part of this work was
done while the author was participating in a program at the Simons Institute for the Theory of
Computing.

<!-- vim: set tw=100 spell spelllang=en : -->

