#include <gcs/current_state.hh>
#include <gcs/expression.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <fstream>
#include <string>
#include <version>

using namespace gcs;

using std::getline;
using std::ifstream;
using std::string;

// GCS_VERBOSE_LOGGING makes ProofLogger::log_stacktrace() prefix each emitted
// proof line with comment lines naming the gcs source frames that produced it
// (see README.md and dev_docs/constraints.md). Resolving those frames needs at
// least line-number debug info in the binary; the Release build ships -g1
// precisely so this stays useful in optimised builds.
//
// The frame filter keys on source_file().contains("/gcs/"), so with no debug
// info source_file() is empty and *nothing* is logged. This test guards against
// exactly that on the platforms where <stacktrace> exists: it catches both the
// feature silently breaking and a build that strips the debug info it needs.
TEST_CASE("Verbose logging names gcs stack frames in the proof")
{
    // do_logging inside log_stacktrace() is read once, on the first call, so the
    // environment has to be set before the first solve in this process.
    setenv("GCS_VERBOSE_LOGGING", "1", 1);

    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i); // unsat: forces inference + proof lines

    solve(p, [&](const CurrentState &) -> bool { return true; }, ProofOptions{"stacktrace_logging_test"});

#ifdef __cpp_lib_stacktrace
    ifstream proof{"stacktrace_logging_test.pbp"};
    REQUIRE(proof);

    bool saw_gcs_frame = false;
    string line;
    while (getline(proof, line))
        if (line.starts_with("% ") && line.find("/gcs/") != string::npos) {
            saw_gcs_frame = true;
            break;
        }

    // <stacktrace> is available on this toolchain, so verbose logging must have
    // named at least one gcs frame. If it did not, either the feature broke or
    // the build dropped the debug info that source_file() resolution depends on.
    CHECK(saw_gcs_frame);
#else
    // No <stacktrace> here (e.g. macOS libc++): log_stacktrace() is compiled out,
    // so there is nothing to assert. Recorded as a pass on those platforms.
    SUCCEED("<stacktrace> unavailable on this toolchain; verbose frame logging is compiled out");
#endif
}
