#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/current_state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <cstdlib>
#include <fstream>
#include <set>
#include <string>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#endif

using namespace gcs;

using std::getline;
using std::ifstream;
using std::set;
using std::size_t;
using std::stoll;
using std::string;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

// A solution's constraint is deleted once something subsumes it, which is a
// checked deletion because VeriPB's solution rules put what they create into
// the core set. Verification on its own cannot tell that apart from deleting
// nothing: a proof that keeps every solution for ever verifies perfectly well,
// and is exactly what we used to write. So this replays the proof's own
// addressing and asserts the constraints really are deleted.
//
// Both halves are covered, because they work differently: an enumeration,
// whose solx blocking constraints go when the frame above the one that found
// them forgets its level, and an optimisation, whose soli objective-improving
// constraint goes as soon as a strictly better solution supersedes it. The
// optimisation proof is written first and then overwritten by the enumeration
// one, so that exactly one set of proof files is left for
// run_test_and_verify.bash to check and dispose of; the optimisation half's
// deletions are veripb-checked by every optimisation example in the suite.
namespace
{
    // Every rule that introduces a constraint advances VeriPB's id counter;
    // deletions, `core` steps, `e` and comments do not. All of our references
    // are relative to that counter (see relative_proof_line), so replaying it
    // from any starting point resolves them: a constant offset from not knowing
    // how many rows the OPB had cancels on both sides.
    struct ProofAddressing
    {
        long long counter = 0;
        vector<long long> solution_constraints;
        set<long long> deleted;
        long long core_steps = 0;
        bool understood = true;

        [[nodiscard]] auto resolve(long long relative) const -> long long
        {
            return counter + relative + 1;
        }
    };

    [[nodiscard]] auto tokens_of(const string & line) -> vector<string>
    {
        vector<string> result;
        string current;
        for (auto c : line) {
            if (c == ' ' || c == '\t' || c == ';') {
                if (! current.empty()) {
                    result.push_back(current);
                    current.clear();
                }
            }
            else
                current += c;
        }
        if (! current.empty())
            result.push_back(current);
        return result;
    }

    [[nodiscard]] auto replay(const string & proof_file) -> ProofAddressing
    {
        ProofAddressing state;
        ifstream proof{proof_file};

        for (string line; getline(proof, line);) {
            auto words = tokens_of(line);
            if (words.empty())
                continue;

            const auto & rule = words[0];
            if (rule.starts_with("%") || rule.starts_with("*") || rule == "pseudo-Boolean" || rule == "output" || rule == "conclusion" ||
                rule == "end" || rule == "e")
                continue;

            if (rule == "begin" || rule == "proofgoal" || rule == "qed") {
                // Nested contexts have their own id space, which this does not
                // model. Fail loudly rather than measure the wrong thing.
                print(stderr, "replay does not model subproofs, and `{}` appeared\n", rule);
                state.understood = false;
                return state;
            }

            if (rule == "core")
                ++state.core_steps;
            else if (rule == "del") {
                if (words.at(1) == "id")
                    for (auto n = words.begin() + 2; n != words.end(); ++n)
                        state.deleted.insert(state.resolve(stoll(*n)));
                else if (words.at(1) == "range")
                    for (auto id = state.resolve(stoll(words.at(2))); id != state.resolve(stoll(words.at(3))); ++id)
                        state.deleted.insert(id);
            }
            else {
                ++state.counter;
                if (rule == "solx" || rule == "soli")
                    state.solution_constraints.push_back(state.counter);
            }
        }

        return state;
    }

    // The enumeration half has to move the backtrack clause and the encoding
    // definitions into core before it can delete anything; the optimisation
    // half needs nothing moved, because the constraint that discharges its
    // deletion goal is the one the new soli itself put into core.
    enum class NeedsCoreSteps
    {
        Yes,
        No
    };

    [[nodiscard]] auto check(const string & what, const ProofAddressing & state, size_t expected_solutions, size_t expected_deleted,
        NeedsCoreSteps needs_core_steps) -> bool
    {
        auto ok = state.understood;

        if (state.solution_constraints.size() != expected_solutions) {
            print(stderr, "{}: proof logs {} solutions, solving found {}\n", what, state.solution_constraints.size(), expected_solutions);
            ok = false;
        }

        size_t deleted = 0;
        for (auto id : state.solution_constraints)
            if (state.deleted.contains(id))
                ++deleted;

        if (deleted != expected_deleted) {
            print(stderr, "{}: {} of {} solution constraints deleted, expected {}\n", what, deleted, state.solution_constraints.size(),
                expected_deleted);
            ok = false;
        }

        if (NeedsCoreSteps::Yes == needs_core_steps && 0 == state.core_steps) {
            print(stderr, "{}: nothing was moved to core, so nothing could have been checked-deleted\n", what);
            ok = false;
        }

        return ok;
    }
}

auto main() -> int
{
    auto ok = true;

    {
        // Maximising, so that the default smallest-value-first branching meets
        // the objective from the wrong end and branch and bound logs a chain of
        // improving solutions rather than hitting the optimum first. Every one
        // but the last is superseded and deleted.
        Problem p;
        auto x = p.create_integer_variable(0_i, 5_i, "x");
        auto y = p.create_integer_variable(0_i, 5_i, "y");
        p.post(LessThan{y, x});
        p.maximise(y);

        auto stats = solve_with(p, SolveCallbacks{}, ProofOptions{"solution_deletion_test"});

        auto state = replay("solution_deletion_test.pbp");
        if (stats.solutions < 2) {
            print(stderr, "optimisation: only {} solutions logged, so nothing could be superseded\n", stats.solutions);
            ok = false;
        }
        else
            ok = check("optimisation", state, stats.solutions, stats.solutions - 1, NeedsCoreSteps::No) && ok;
    }

    {
        // An enumeration deep enough that every solution is found below a frame
        // whose parent forgets the level it lives at. A solution reached at
        // depth 1 would land at Top and stay, which is correct but would make
        // the count below wrong, so there are three variables to branch on.
        Problem p;
        auto x = p.create_integer_variable(0_i, 2_i, "x");
        auto y = p.create_integer_variable(0_i, 2_i, "y");
        auto z = p.create_integer_variable(0_i, 2_i, "z");
        p.post(NotEquals{x, y});
        p.post(NotEquals{y, z});

        auto stats =
            solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }}, ProofOptions{"solution_deletion_test"});

        ok = check("enumeration", replay("solution_deletion_test.pbp"), stats.solutions, stats.solutions, NeedsCoreSteps::Yes) && ok;
    }

    return ok ? EXIT_SUCCESS : EXIT_FAILURE;
}
