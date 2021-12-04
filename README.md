The Glasgow Constraint Solver
=============================

This will one day be a full fledged constraint programming solver, but currently it is a playground
for whatever half-baked ideas pop into my head. You probably don't want to use this yet, but if you
do, look in the examples directory.

Please contact [Ciaran McCreesh](mailto:ciaran.mccreesh@glasgow.ac.uk) with any queries.

Compiling
---------

To build, type 'make'. You will need a C++20 compiler, such as GCC 10.3, as well as Boost (use
libboost-dev-all on Ubuntu).

Proof Logging
-------------

The key feature of this solver is (or at least will be) the ability to produce proof logs. Currently
we are using the VeriPB format. You can find out more here:

* VeriPB from https://github.com/StephanGocht/VeriPB/ .


Funding Acknowledgements
------------------------

This work is supported by a Royal Academy of Engineering Research Fellowship. Part of this work was
done while the author was participating in a program at the Simons Institute for the Theory of
Computing.

<!-- vim: set tw=100 spell spelllang=en : -->

