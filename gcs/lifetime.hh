#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LIFETIME_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_LIFETIME_HH

/**
 * \file
 * \brief Lifetime-annotation macros for the public API.
 *
 * Several parts of the API hand out handles, references, or pointers that are
 * only valid for as long as some other object is alive. Where clang provides
 * lifetime attributes, we use them to turn misuse of these contracts into
 * compile-time `-Wdangling` warnings at the call site; the analysis is purely
 * static, and the attributes have no effect on ABI or semantics. On compilers
 * without the attributes, these macros expand to nothing.
 *
 * GCS_LIFETIME_BOUND marks a function parameter (including the implicit this
 * parameter, when placed after the parameter list) whose referent the return
 * value points into: the result must not outlive that argument.
 *
 * GCS_GSL_POINTER marks a class type that behaves like a non-owning pointer
 * or view into some other object, so that the analysis tracks what it points
 * to across initialisations.
 */

#if defined(__has_cpp_attribute)
#if __has_cpp_attribute(clang::lifetimebound)
#define GCS_LIFETIME_BOUND [[clang::lifetimebound]]
#endif
#if __has_cpp_attribute(gsl::Pointer)
#define GCS_GSL_POINTER [[gsl::Pointer]]
#endif
#endif

#ifndef GCS_LIFETIME_BOUND
#define GCS_LIFETIME_BOUND
#endif

#ifndef GCS_GSL_POINTER
#define GCS_GSL_POINTER
#endif

#endif
