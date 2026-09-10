#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/proof.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <exception>
#include <fstream>
#include <iterator>
#include <optional>
#include <string>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

using namespace gcs;
using namespace gcs::test_innards;

using std::ifstream;
using std::istreambuf_iterator;
using std::make_optional;
using std::string;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

// The proof stream writes through a 1MB buffer that ProofLogger::Imp owns and
// installs with pubsetbuf, so the bytes of a .pbp live in that buffer until
// something flushes them. end_proof() flushes explicitly, which is why a proof
// that runs to completion is always whole; a solve that throws part-way through
// never reaches end_proof, and the only flush left is the one ~fstream does when
// it closes the file.
//
// That flush must still be able to read the buffer, which makes the declaration
// order of those two members load-bearing: members are destroyed in reverse, so
// the buffer has to be declared first to outlive the stream. It was not, and the
// consequence was invisible --- the final write read freed memory, and where the
// 1MB block had been handed back to the kernel the write failed with EFAULT and
// dropped the whole unflushed tail of the .pbp on the floor without a word.
//
// So: throw out of a solve that is writing a proof, and check the proof written
// so far actually reached the disk.
namespace
{
    struct ThrowFromSolution final : std::exception
    {
    };
}

auto main() -> int
{
    const string base = "proof_flush_on_throw_test";

    Problem p;
    auto x = p.create_integer_variable(0_i, 3_i, "x");
    auto y = p.create_integer_variable(0_i, 3_i, "y");
    p.post(LessThan{x, y});

    auto threw = false;
    try {
        static_cast<void>(solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { throw ThrowFromSolution{}; }},
            make_optional<ProofOptions>(ProofFileNames{base})));
    }
    catch (const ThrowFromSolution &) {
        threw = true;
    }

    auto ok = true;

    if (! threw) {
        print(stderr, "the solution callback's exception did not escape solve_with\n");
        ok = false;
    }

    // Read after the solve, so the ProofLogger --- and with it the stream whose
    // destructor does the flush --- has been destroyed.
    ifstream proof{base + ".pbp"};
    const string contents{istreambuf_iterator<char>{proof}, istreambuf_iterator<char>{}};

    if (! proof) {
        print(stderr, "could not read {}.pbp\n", base);
        ok = false;
    }
    else if (contents.empty()) {
        // What the lost-tail bug looked like: everything written before the throw
        // fitted in the buffer, and none of it survived the close.
        print(stderr, "{}.pbp is empty: the buffered proof never reached the disk\n", base);
        ok = false;
    }
    else {
        // A partially-written proof is expected and fine. Corrupt bytes at the
        // front are not: freeing the buffer before the flush leaves the
        // allocator's own bookkeeping in the first few bytes of it.
        const string header = "pseudo-Boolean proof version 3.0\n";
        if (! contents.starts_with(header)) {
            print(stderr, "{}.pbp does not begin with the version header: {:?}\n", base, contents.substr(0, header.size()));
            ok = false;
        }
        // Nothing writes a partial line, so a whole flush ends at a line ending.
        if (contents.back() != '\n') {
            print(stderr, "{}.pbp does not end at a line ending\n", base);
            ok = false;
        }
    }

    proof.close();
    dispose_of_proof_files(base);

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
