#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_GENERATOR_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_UTIL_GENERATOR_HH

/**
 * \file
 * \brief `std::generator`, from the standard library where it exists and from a
 * vendored shim where it does not.
 *
 * The tree uses `std::generator` for the coroutine-based enumeration APIs
 * (`Problem::each_constraint`, `NamesAndIDsTracker::each_bit`, and friends).
 * libstdc++ has had it since GCC 14 and MSVC since VS 2022; libc++ has not
 * shipped it at all, as of LLVM 22.
 *
 * Include this rather than either of the two directly: the choice of which one
 * belongs in one place, and it used to be repeated at seven call sites with a
 * fetched-at-configure-time dependency behind it. See
 * dev_docs/building.md, "The vendored <generator> shim", for why the shim is
 * vendored rather than fetched, and for the one thing it deliberately does not
 * support.
 */

#include <version>

#ifdef __cpp_lib_generator
#include <generator>
#else
#include <util/p2168_generator.hpp>
#endif

#endif
