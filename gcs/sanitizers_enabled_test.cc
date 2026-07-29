#include <catch2/catch_test_macros.hpp>

// Guards the Sanitize build type against silently containing no sanitizers.
//
// This is not a hypothetical. Under CMake 4.2 the cached set() that supplied
// -fsanitize=address,undefined was a no-op, so `cmake --preset sanitize` built
// an ordinary -O1 tree and the CI lane reported "sanitize clean" for months
// without a sanitizer ever running (issue #597). Nothing warned: the flags were
// simply absent. The top-level CMakeLists.txt now fails the configure if
// CMAKE_CXX_FLAGS_SANITIZE has lost its -fsanitize flag; this test checks the
// far end of the same chain, that the flag actually reached the compiler.
//
// GCS_CONFIG_IS_SANITIZE is defined by gcs/CMakeLists.txt only for the Sanitize
// configuration on non-MSVC compilers, so in every other build this file compiles
// to a test that trivially passes.
//
// The compiler tells us what it was asked to instrument in two different ways:
// clang, and GCC from 14 onwards, answer __has_feature(); older GCC only defines
// __SANITIZE_ADDRESS__. Accept either. UBSan has no __SANITIZE_UNDEFINED__
// equivalent, so it can only be checked where __has_feature() exists -- but both
// sanitizers come from the same -fsanitize=address,undefined flag, so ASan being
// present already establishes that the flag arrived intact.

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define GCS_ASAN_PRESENT
#endif
#if __has_feature(undefined_behavior_sanitizer)
#define GCS_UBSAN_PRESENT
#endif
#define GCS_UBSAN_DETECTABLE
#endif

#if defined(__SANITIZE_ADDRESS__) && ! defined(GCS_ASAN_PRESENT)
#define GCS_ASAN_PRESENT
#endif

TEST_CASE("A Sanitize build really is built with sanitizers")
{
#if ! defined(GCS_CONFIG_IS_SANITIZE)
    SUCCEED("not a Sanitize build, nothing to check");
#else
#if ! defined(GCS_ASAN_PRESENT)
    FAIL("This is a Sanitize build, but AddressSanitizer is not compiled in: the "
         "-fsanitize=address,undefined flag never reached the compiler. Everything "
         "this build type exists to catch is going undetected, and every result from "
         "it is meaningless. Fix the flag handling in CMakeLists.txt -- do not relax "
         "this test. See issue #597 for how it happened last time.");
#elif defined(GCS_UBSAN_DETECTABLE) && ! defined(GCS_UBSAN_PRESENT)
    FAIL("This is a Sanitize build with AddressSanitizer but without "
         "UndefinedBehaviorSanitizer, so undefined behaviour is going undetected. "
         "Restore ,undefined in CMAKE_CXX_FLAGS_SANITIZE in CMakeLists.txt.");
#else
    SUCCEED("sanitizers are compiled in");
#endif
#endif
}
