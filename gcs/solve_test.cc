#include <gcs/constraints/all_different.hh>
#include <gcs/constraints/comparison.hh>
#include <gcs/constraints/difference.hh>
#include <gcs/constraints/divide.hh>
#include <gcs/constraints/element.hh>
#include <gcs/constraints/equals.hh>
#include <gcs/constraints/in.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/modulus.hh>
#include <gcs/constraints/plus.hh>
#include <gcs/constraints/power.hh>
#include <gcs/constraints/table.hh>
#include <gcs/expression.hh>
#include <gcs/presolver.hh>
#include <gcs/presolvers/auto_table.hh>
#include <gcs/problem.hh>
#include <gcs/solve.cc>

#include <catch2/catch_test_macros.hpp>

#include <cstdlib>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

using std::function;
using std::nullopt;
using std::optional;
using std::string;
using std::vector;

namespace
{
    // Toggle the GCS_LEARNED_NOGOODS_SCAN env var (read by solve.cc to select the
    // legacy whole-store-scan nogood path) portably: MSVC has no POSIX setenv /
    // unsetenv, and on Windows _putenv_s(name, "") removes the variable.
    auto set_learned_nogoods_scan(bool on) -> void
    {
#if defined(_WIN32)
        _putenv_s("GCS_LEARNED_NOGOODS_SCAN", on ? "1" : "");
#else
        if (on)
            setenv("GCS_LEARNED_NOGOODS_SCAN", "1", 1);
        else
            unsetenv("GCS_LEARNED_NOGOODS_SCAN");
#endif
    }
}

// Every proving case below uses its own proof basename rather than a shared
// one. verify_proof_and_dispose() keeps the files when a proof fails to verify,
// but Catch2's CHECK is non-fatal, so the run carries on into the next case: a
// shared basename would have that case's solve() overwrite the failing proof
// microseconds later, leaving artifacts belonging to whichever case ran last.
// Distinct names also make GCS_PRESERVE_PROOF_FILES=1 yield a usable set from
// this binary rather than a single file.
TEST_CASE("Solve unsat")
{
    const auto proof_name = "solve_test_unsat";

    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i);

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(verify_proof_and_dispose(proof_name));
}

TEST_CASE("Solve unsat by model optimisation")
{
    const auto proof_name = "solve_test_unsat_model_optimisation";

    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(LessThan{1_c, 0_c});
    p.maximise(v);

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(verify_proof_and_dispose(proof_name));
}

// Four variables over three values, pairwise different: unsatisfiable, and
// posted as weak pairwise NotEquals (no Hall pruning) so search must branch and
// hit conflicts rather than wiping out at the root. A luby(1) schedule then
// restarts after almost every conflict, so the search only terminates because
// the growing cutoff eventually exceeds the whole tree --- exercising the
// restart loop and that the proof stays balanced across many restarts.
TEST_CASE("Solve unsat with restarts")
{
    const auto proof_name = "solve_test_unsat_restarts";

    Problem p;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 4; ++i)
        xs.push_back(p.create_integer_variable(0_i, 2_i));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            p.post(NotEquals{xs[i], xs[j]});

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    // Restarts learn nogoods from the refuted regions, and the proof verifies
    // those learned clauses (an unsound one would fail RUP).
    CHECK(stats.learned_nogoods > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

// As "Solve unsat with restarts" but with binary (2-way) branching:
// value_order::smallest_in yields x==v then x!=v, and the right branch x!=v is
// the negation of the left. Reduced nld-nogoods drop that refutation-flip from
// the recorded path, so this exercises the reduced-extraction code that the
// d-way default branching above leaves untouched. The proof still verifies --- an
// unsound reduction (dropping a literal that is not re-derivable) fails RUP.
TEST_CASE("Solve unsat with restarts and binary branching")
{
    const auto proof_name = "solve_test_unsat_restarts_binary";

    Problem p;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 5; ++i)
        xs.push_back(p.create_integer_variable(0_i, 3_i));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            p.post(NotEquals{xs[i], xs[j]});

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .branch = branch_with(variable_order::dom(p), value_order::smallest_in()),
            .restarts = RestartSchedule::luby(4)},
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(stats.learned_nogoods > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

// As above but with interval (bound-split) branching: value_order::
// split_smallest_first yields x<=v then x>v, and x>v is the negation of x<=v
// (both are order literals, not equalities). The reduced nld-nogoods drop that
// flip just as for the equality case, exercising the bound-literal path of the
// extraction and the entailment 2WL. The proof still verifies.
TEST_CASE("Solve unsat with restarts and interval branching")
{
    const auto proof_name = "solve_test_unsat_restarts_interval";

    Problem p;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 5; ++i)
        xs.push_back(p.create_integer_variable(0_i, 3_i));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            p.post(NotEquals{xs[i], xs[j]});

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .branch = branch_with(variable_order::dom(p), value_order::split_smallest_first()),
            .restarts = RestartSchedule::luby(4)},
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(stats.learned_nogoods > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

// As above but with reject-interval branching: value_order::reject_random_interval
// yields genuine range-condition decisions --- x not_in [lo..hi] then x in [lo..hi],
// the in/out interval-literal vocabulary the range-literal foundation added. Unlike
// the equality, order and bound-split cases above, this drives the whole restart +
// nogood pipeline (guess -> learned-nogood extraction -> reduced-nld -> RUP, plus the
// refined per-literal 2WL watching the learned store) on InRange / NotInRange
// literals, confirming the nogood machinery's test_literal-based watching is range-
// operator-agnostic. The proof must still verify.
TEST_CASE("Solve unsat with restarts and reject-interval branching")
{
    const auto proof_name = "solve_test_unsat_restarts_reject_interval";

    Problem p;
    vector<IntegerVariableID> xs;
    for (int i = 0; i < 5; ++i)
        xs.push_back(p.create_integer_variable(0_i, 3_i));
    for (unsigned i = 0; i < xs.size(); ++i)
        for (unsigned j = i + 1; j < xs.size(); ++j)
            p.post(NotEquals{xs[i], xs[j]});

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .branch = branch_with(variable_order::dom(p), value_order::reject_random_interval(1)),
            .restarts = RestartSchedule::luby(4)},
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(stats.learned_nogoods > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

// Optimisation with restarts: the incumbent bound persists across restarts, so
// each pass only finds strictly better solutions and the final pass proves
// optimality. Objective-bound dead-ends count as conflicts, so a luby(1)
// schedule restarts here too.
TEST_CASE("Optimise with restarts")
{
    const auto proof_name = "solve_test_optimise_restarts";

    Problem p;
    auto x = p.create_integer_variable(0_i, 2_i);
    auto y = p.create_integer_variable(0_i, 2_i);
    auto z = p.create_integer_variable(0_i, 2_i);
    p.post(NotEquals{x, y});
    p.post(NotEquals{x, z});
    p.post(NotEquals{y, z});
    p.maximise(x);

    optional<Integer> best = nullopt;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           best = s(x);
                           return true;
                       },
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{proof_name});

    CHECK(best == optional<Integer>{2_i});
    CHECK(stats.restarts > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

// Scan-vs-refined differential for the engine-owned learned-nogood store (issue
// #335, stage C-2). The refined per-literal-watch path (the default) must explore
// the identical search and learn the identical nogoods as the legacy whole-store-
// scan path (selected by GCS_LEARNED_NOGOODS_SCAN), since the conversion is
// semantics-preserving. We drive a pigeonhole UNSAT (6 values into 5) with a
// luby(1) schedule -- many restarts, a growing nogood store, and the growable
// catch-up exercised at every restart root -- under deterministic, domain-based
// (degree-independent) branching, and require byte-identical search statistics.
// A missed or spurious inference on the refined path would change the tree.
TEST_CASE("Learned nogoods: refined matches scan under restarts")
{
    auto run = [](bool scan) -> Stats {
        set_learned_nogoods_scan(scan);

        Problem p;
        vector<IntegerVariableID> xs;
        for (int i = 0; i < 6; ++i)
            xs.push_back(p.create_integer_variable(0_i, 4_i));
        for (unsigned i = 0; i < xs.size(); ++i)
            for (unsigned j = i + 1; j < xs.size(); ++j)
                p.post(NotEquals{xs[i], xs[j]});

        return solve_with(p,
            SolveCallbacks{.branch = branch_with(variable_order::dom(p), value_order::smallest_in()), .restarts = RestartSchedule::luby(1)}, nullopt);
    };

    auto refined = run(false);
    auto scan = run(true);
    set_learned_nogoods_scan(false);

    // The instance must actually restart and learn, or the differential is vacuous.
    CHECK(refined.restarts > 0);
    CHECK(refined.learned_nogoods > 0);

    CHECK(refined.recursions == scan.recursions);
    CHECK(refined.failures == scan.failures);
    CHECK(refined.restarts == scan.restarts);
    CHECK(refined.learned_nogoods == scan.learned_nogoods);
    CHECK(refined.solutions == scan.solutions);
}

// An unsatisfiable Langford-pairing instance (size 5): rich enough that
// AllDifferent and Element prune at the root, so the root node emits
// guess-independent propagation that later restart passes do not re-derive.
// This guards the fix that keeps that root reasoning (proof level 1) across
// restarts; the NotEquals cases above have too little root propagation to
// exercise it. The luby scale is chosen so a couple of restarts fire before the
// growing cutoff exhausts the tree.
TEST_CASE("Solve unsat with restarts and root propagation")
{
    const auto proof_name = "solve_test_unsat_restarts_root_propagation";

    Problem p;
    const int k = 5;
    vector<IntegerVariableID> position, solution;
    for (int i = 0; i < 2 * k; ++i) {
        position.emplace_back(p.create_integer_variable(0_i, Integer{2 * k - 1}));
        solution.emplace_back(p.create_integer_variable(1_i, Integer{k}));
    }
    p.post(AllDifferent{position});
    for (int i = 0; i < k; ++i) {
        auto i_var = p.create_integer_variable(Integer{i + 1}, Integer{i + 1});
        p.post(Element{i_var, position[i], &solution});
        p.post(Element{i_var, position[i + k], &solution});
        p.post(Plus{position[i + k], constant_variable(Integer{i + 2}), position[i]}.with_consistency(consistency::Tabulated{}));
    }

    bool found_solution = false;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState &) -> bool {
                           found_solution = true;
                           return false;
                       },
            .restarts = RestartSchedule::luby(10)},
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(stats.restarts > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

// Enumerate every solution while restarting. b, c, d are a pairwise-distinct
// triangle (a permutation of {1,2,3}) and a (domain 1..4) must differ from all
// three, forcing a = 4 --- so there are six solutions. But a branched to 1/2/3
// early leaves b, c, d needing three distinct values in the two that remain: a
// dead end. Random branching hits those, so a luby(1) schedule restarts
// part-way through enumeration. Each solution must still be reported exactly
// once: the nld nogoods, sound because solx excludes the solutions already
// found, stop a later pass re-entering an exhausted region. The proof must
// conclude a complete enumeration of six.
TEST_CASE("Enumerate all solutions with restarts")
{
    const auto proof_name = "solve_test_enumerate_restarts";

    Problem p;
    auto a = p.create_integer_variable(1_i, 4_i);
    auto b = p.create_integer_variable(1_i, 3_i);
    auto c = p.create_integer_variable(1_i, 3_i);
    auto d = p.create_integer_variable(1_i, 3_i);
    p.post(NotEquals{a, b});
    p.post(NotEquals{a, c});
    p.post(NotEquals{a, d});
    p.post(NotEquals{b, c});
    p.post(NotEquals{b, d});
    p.post(NotEquals{c, d});

    std::set<std::tuple<int, int, int, int>> solutions;
    unsigned long long callbacks = 0;
    auto stats = solve_with(p,
        SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                           ++callbacks;
                           solutions.emplace(s(a).raw_value, s(b).raw_value, s(c).raw_value, s(d).raw_value);
                           return true;
                       },
            .branch = branch_with(variable_order::random(p, 1234), value_order::random_out(5678)),
            .restarts = RestartSchedule::luby(1)},
        ProofOptions{proof_name});

    CHECK(solutions.size() == 6);
    CHECK(callbacks == 6); // each solution reported exactly once, no re-counting
    CHECK(stats.solutions == 6);
    CHECK(stats.restarts > 0); // restarts actually fired during enumeration
    CHECK(stats.learned_nogoods > 0);
    CHECK(verify_proof_and_dispose(proof_name));
}

TEST_CASE("Solve unsat optimisation presolving")
{
    const auto proof_name = "solve_test_unsat_optimisation_presolving";

    Problem p;
    auto v = p.create_integer_variable(0_i, 100_i);
    p.post(WeightedSum{} + 1_i * v >= 200_i);
    p.add_presolver(AutoTable{vector<IntegerVariableID>{v}});

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{proof_name});

    CHECK(! found_solution);
    CHECK(verify_proof_and_dispose(proof_name));
}

namespace
{
    // A presolver that installs initialisers, to pin that they run: a presolver
    // may install a constraint, and a constraint does its once-only work ---
    // introducing a proof-only variable, say --- in an initialiser. Before
    // this, one installed from a presolver was dropped without a word, because
    // solve() had already run the initialisers by the time presolvers were
    // called.
    struct InitialiserInstallingPresolver : Presolver
    {
        std::shared_ptr<unsigned> ran;
        std::shared_ptr<unsigned> ran_before_next_presolver;
        bool contradict = false;
        bool install_another = false;

        [[nodiscard]] auto run(Problem &, innards::Propagators & propagators, innards::State &, innards::ProofLogger * const) -> bool override
        {
            propagators.install_initialiser([ran = ran, contradict = contradict, install_another = install_another, &propagators](
                                                const innards::State &, auto & inference, innards::ProofLogger * const logger) -> void {
                ++*ran;
                if (logger)
                    logger->emit_proof_comment("initialiser installed by a presolver");
                if (install_another)
                    propagators.install_initialiser([ran = ran](const innards::State &, auto &, innards::ProofLogger * const) -> void { ++*ran; },
                        innards::InitialiserPriority::SimpleDefinition);
                if (contradict)
                    inference.contradiction(logger, JustifyUsingRUP{}, NoReason{});
            });
            return true;
        }

        [[nodiscard]] auto clone() const -> std::unique_ptr<Presolver> override
        {
            return std::make_unique<InitialiserInstallingPresolver>(*this);
        }
    };

    // Runs second, and records what the first one's initialiser had done by
    // then.
    struct ObservingPresolver : Presolver
    {
        std::shared_ptr<unsigned> ran;
        std::shared_ptr<unsigned> observed;

        [[nodiscard]] auto run(Problem &, innards::Propagators &, innards::State &, innards::ProofLogger * const) -> bool override
        {
            *observed = *ran;
            return true;
        }

        [[nodiscard]] auto clone() const -> std::unique_ptr<Presolver> override
        {
            return std::make_unique<ObservingPresolver>(*this);
        }
    };
}

TEST_CASE("An initialiser installed by a presolver runs")
{
    const auto proof_name = "solve_test_presolver_initialiser";
    auto ran = std::make_shared<unsigned>(0);

    Problem p;
    auto v = p.create_integer_variable(0_i, 3_i);
    p.post(WeightedSum{} + 1_i * v >= 0_i);

    InitialiserInstallingPresolver presolver;
    presolver.ran = ran;
    p.add_presolver(presolver);

    unsigned solutions = 0;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            ++solutions;
            return true;
        },
        ProofOptions{proof_name});

    CHECK(*ran == 1); // exactly once: not dropped, and not re-run per node
    CHECK(solutions == 4);
    CHECK(verify_proof_and_dispose(proof_name)); // and what it wrote is part of a verifiable proof
}

TEST_CASE("A presolver's initialiser runs before the next presolver")
{
    auto ran = std::make_shared<unsigned>(0);
    auto observed = std::make_shared<unsigned>(0);

    Problem p;
    auto v = p.create_integer_variable(0_i, 3_i);
    p.post(WeightedSum{} + 1_i * v >= 0_i);

    InitialiserInstallingPresolver first;
    first.ran = ran;
    p.add_presolver(first);

    ObservingPresolver second;
    second.ran = ran;
    second.observed = observed;
    p.add_presolver(second);

    solve(p, [&](const CurrentState &) -> bool { return true; });

    CHECK(*observed == 1); // the second presolver saw a fully initialised problem
}

TEST_CASE("An initialiser installed by an initialiser runs")
{
    auto ran = std::make_shared<unsigned>(0);

    Problem p;
    auto v = p.create_integer_variable(0_i, 3_i);
    p.post(WeightedSum{} + 1_i * v >= 0_i);

    InitialiserInstallingPresolver presolver;
    presolver.ran = ran;
    presolver.install_another = true;
    p.add_presolver(presolver);

    solve(p, [&](const CurrentState &) -> bool { return true; });

    CHECK(*ran == 2); // the one the presolver installed, and the one that installed
}

TEST_CASE("A presolver's initialiser can report unsatisfiability")
{
    const auto proof_name = "solve_test_presolver_initialiser_contradiction";
    auto ran = std::make_shared<unsigned>(0);

    // Genuinely unsatisfiable, so the contradiction the initialiser raises is
    // one reverse unit propagation can reach: two constraints that are each
    // fine on their own, so nothing detects it before the presolver runs.
    Problem p;
    auto a = p.create_integer_variable(0_i, 3_i);
    auto b = p.create_integer_variable(0_i, 3_i);
    p.post(WeightedSum{} + 1_i * a + 1_i * b >= 5_i);
    p.post(WeightedSum{} + 1_i * a + 1_i * b <= 1_i);

    InitialiserInstallingPresolver presolver;
    presolver.ran = ran;
    presolver.contradict = true;
    p.add_presolver(presolver);

    bool found_solution = false;
    solve(
        p,
        [&](const CurrentState &) -> bool {
            found_solution = true;
            return false;
        },
        ProofOptions{proof_name});

    CHECK(*ran == 1);
    CHECK(! found_solution); // a contradiction there ends the solve, rather than being lost
    CHECK(verify_proof_and_dispose(proof_name));
}

namespace
{
    /// The number of fields in a stats block, worked out from its size.
    ///
    /// Every field of these blocks is eight bytes wide --- a `std::size_t`, an
    /// `Integer`, a nested block of `std::size_t`s, or a `bool` that pads out to
    /// the next one --- and the only other thing in the object is the vtable
    /// pointer this design's base class brings. So `sizeof` counts the fields,
    /// and a field added without a matching `entries()` line moves one side of
    /// the comparison below and not the other. That is the rot this design can
    /// grow: a figure that exists, is filled in, and reaches nobody.
    template <typename Block_>
    [[nodiscard]] auto field_count() -> std::size_t
    {
        static_assert(0 == (sizeof(Block_) - sizeof(void *)) % sizeof(std::size_t),
            "this block has a field that is not eight bytes wide, so "
            "counting its fields needs doing another way");
        return (sizeof(Block_) - sizeof(void *)) / sizeof(std::size_t);
    }

    /// A recording StatsReportCallback. Tests assert on the notes rather than on
    /// rendered output, because a note's *level* is what rendering throws away
    /// and a level quietly drifting down to Detailed is what would undo this
    /// channel with nothing else noticing.
    struct Recorder
    {
        std::shared_ptr<std::vector<StatsNote>> notes = std::make_shared<std::vector<StatsNote>>();

        [[nodiscard]] auto callback() const -> StatsReportCallback
        {
            return [notes = notes](const StatsNote & note) -> void { notes->push_back(note); };
        }

        [[nodiscard]] auto at_level(StatsLevel level) const -> std::vector<StatsNote>
        {
            std::vector<StatsNote> result;
            for (const auto & note : *notes)
                if (note.level == level)
                    result.push_back(note);
            return result;
        }
    };

    [[nodiscard]] auto component_named(const Stats & stats, const std::string & name) -> std::shared_ptr<const ComponentStats>
    {
        for (const auto & component : stats.components())
            if (component->component_name() == name)
                return component;
        return nullptr;
    }
}

TEST_CASE("A note is rendered with its component label, except at Important")
{
    // The component label is for someone who knows what the component is, and
    // an Important note is written for someone who does not.
    CHECK(render(StatsNote{StatsLevel::General, "auto_table", nullopt, "did a thing"}) == "auto_table: did a thing");
    CHECK(render(StatsNote{StatsLevel::Important, "auto_table", nullopt, "did a thing"}) == "did a thing");

    // The ConstraintID is on the note rather than baked into the text, so that
    // a caller can filter and a test can assert; putting it into words is the
    // renderer's job.
    CHECK(render(StatsNote{StatsLevel::General, "auto_table", ConstraintID{NumberedConstraint{7}}, "did a thing"}) == "auto_table: did a thing (_7)");
}

TEST_CASE("Stats accumulates notes and forwards them as they happen")
{
    Stats stats;

    std::vector<StatsLevel> seen;
    stats.set_report_handler([&](const StatsNote & note) -> void { seen.push_back(note.level); });

    stats.report(StatsNote{StatsLevel::Debug, "a", nullopt, "one"});
    stats.report(StatsNote{StatsLevel::Important, "a", nullopt, "two"});

    // Forwarded at the moment of reporting, in order, and kept.
    CHECK(seen == std::vector<StatsLevel>{StatsLevel::Debug, StatsLevel::Important});
    CHECK(stats.notes().size() == 2);

    // The default callback filters by level rather than reporting everything.
    std::ostringstream captured;
    auto old = std::cerr.rdbuf(captured.rdbuf());
    auto reporter = default_stats_report();
    reporter(StatsNote{StatsLevel::General, "a", nullopt, "quiet"});
    reporter(StatsNote{StatsLevel::Important, "a", nullopt, "loud"});
    std::cerr.rdbuf(old);
    CHECK(captured.str() == "loud\n");
}

TEST_CASE("Registering the same component block twice reports it once")
{
    // A constraint installed many times, or a presolver whose block is shared
    // with a caller who also registered it, should be one line and not N.
    struct Block final : ComponentStats
    {
        [[nodiscard]] auto component_name() const -> std::string override
        {
            return "block";
        }
        [[nodiscard]] auto summary() const -> std::string override
        {
            return "nothing";
        }
        [[nodiscard]] auto entries() const -> std::vector<StatsEntry> override
        {
            return {};
        }
    };

    Stats stats;
    auto block = std::make_shared<Block>();
    stats.add_component(block);
    stats.add_component(block);
    CHECK(stats.components().size() == 1);
}

TEST_CASE("AutoTable reports what it did, with no stats block asked for")
{
    // Default-constructed, deliberately: the always-allocate path is the whole
    // of #662's fix for this presolver, and it is the part with no other
    // observable effect. Before it, the only record that AutoTable ran at all
    // was three proof comments, so with proofs off --- which is here --- a
    // presolver that had quietly stopped firing looked exactly like one that
    // had fired.
    Problem p;
    auto a = p.create_integer_variable(0_i, 3_i);
    auto b = p.create_integer_variable(0_i, 3_i);
    p.post(WeightedSum{} + 1_i * a + 1_i * b == 3_i);
    p.add_presolver(AutoTable{vector<IntegerVariableID>{a, b}});

    Recorder recorder;
    auto stats = solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }, .stats_report = recorder.callback()});

    auto component = component_named(stats, "auto_table");
    REQUIRE(component);
    CHECK(! component->summary().empty());

    // And that it is the block the presolver actually filled in, rather than a
    // fresh one: Problem::add_presolver stores a *clone*, and run() happens on
    // that, so a clone allocating its own block would leave a summary saying
    // nothing while the tabulation went ahead.
    auto entries = component->entries();
    CHECK(entries.size() == field_count<AutoTableStats>());

    std::map<std::string, long long> by_name;
    for (const auto & entry : entries)
        by_name.emplace(entry.name, entry.value);
    CHECK(by_name["ran"] == 1);
    CHECK(by_name["variables"] == 2);
    CHECK(by_name["tuples"] == 4); // a + b == 3, over 0..3
    CHECK(by_name["search_nodes"] > 0);
}

TEST_CASE("A caller's AutoTable stats block is the one that gets filled in and reported")
{
    // Problem::add_presolver stores a *clone*, and run() is called on that, so
    // a clone allocating a fresh block instead of sharing this one would leave
    // the caller's handle reading zero for ever --- while everything visible
    // through Stats::components() carried on looking exactly right, since what
    // is registered there is whatever the clone happens to hold. Pointer
    // identity is what says the two are the same block.
    auto block = std::make_shared<AutoTableStats>();

    Problem p;
    auto a = p.create_integer_variable(0_i, 3_i);
    auto b = p.create_integer_variable(0_i, 3_i);
    p.post(WeightedSum{} + 1_i * a + 1_i * b == 3_i);
    p.add_presolver(AutoTable{vector<IntegerVariableID>{a, b}, block});

    auto stats = solve(p, [](const CurrentState &) -> bool { return true; });

    CHECK(block->ran);
    CHECK(block->tuples == 4);
    CHECK(component_named(stats, "auto_table").get() == static_cast<const ComponentStats *>(block.get()));
}

TEST_CASE("A constraint that is trivially unsatisfiable at install time says which one, and why")
{
    // Six sites --- seven constraints, Divide and Modulus sharing one --- work
    // out while installing that what they encode is the empty relation, and
    // install a contradiction initialiser instead of a propagator. Each has
    // always passed an explanation of what was wrong with it; the parameter that
    // took it was unnamed and dropped it (#722), so the whole visible
    // consequence of `x div 0` was an unsatisfiable answer that looks exactly
    // like a model whose constraints genuinely conflict.
    struct Case
    {
        string component;
        string mentions;
        function<auto(Problem &, IntegerVariableID, IntegerVariableID)->void> post;
    };

    const vector<Case> cases{
        {"table", "no tuples", [](Problem & p, IntegerVariableID x, IntegerVariableID y) { p.post(Table{{x, y}, SimpleTuples{}}); }},
        {"in", "no values", [](Problem & p, IntegerVariableID x, IntegerVariableID) { p.post(In{x, vector<Integer>{}}); }},
        {"element", "zero-length dimension",
            [](Problem & p, IntegerVariableID x, IntegerVariableID y) { p.post(Element{x, y, vector<IntegerVariableID>{}}); }},
        {"power", "overflow", [](Problem & p, IntegerVariableID x, IntegerVariableID) { p.post(Power{0_c, constant_variable(-1_i), x}); }},
        {"divide", "divisor of constant zero", [](Problem & p, IntegerVariableID x, IntegerVariableID y) { p.post(Divide{x, 0_c, y}); }},
        {"modulus", "divisor of constant zero", [](Problem & p, IntegerVariableID x, IntegerVariableID y) { p.post(Modulus{x, 0_c, y}); }},
        {"difference", "strictly less than itself", [](Problem & p, IntegerVariableID x, IntegerVariableID) {
             p.post(DifferenceConstraints{vector<DifferenceEdge>{DifferenceEdge{x, x, -1_i}}});
         }}};

    for (const auto & c : cases) {
        INFO("constraint type " << c.component);

        Problem p;
        auto x = p.create_integer_variable(0_i, 3_i);
        auto y = p.create_integer_variable(0_i, 3_i);
        c.post(p, x, y);

        Recorder recorder;
        auto stats =
            solve_with(p, SolveCallbacks{.solution = [](const CurrentState &) -> bool { return true; }, .stats_report = recorder.callback()});

        CHECK(0 == stats.solutions);

        // Exactly one note, and Important: the reader it is for is the
        // non-expert who cannot otherwise tell "your constraints conflict" from
        // "one of them was empty", and who is reading a solve that got no
        // further than installing this constraint.
        auto important = recorder.at_level(StatsLevel::Important);
        REQUIRE(important.size() == 1);
        CHECK(important[0].component == c.component);
        CHECK(important[0].constraint == ConstraintID{NumberedConstraint{1}});

        // The text names what kind of constraint it was and what was wrong with
        // it, since at Important the component label is not rendered; the
        // consequence is there too, because "unsatisfiable" is the thing the
        // reader is trying to account for. The identity is the note's own field
        // rather than words, and render() is what puts it into the line.
        CHECK(important[0].text.contains(c.mentions));
        CHECK(important[0].text.ends_with(", so the model is unsatisfiable before search starts"));
        CHECK(render(important[0]).ends_with(" (_1)"));
    }
}
