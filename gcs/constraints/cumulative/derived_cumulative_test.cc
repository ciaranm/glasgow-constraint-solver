#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>
#include <gcs/presolver.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <climits>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <numeric>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>
#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/core.h>
#include <fmt/ostream.h>
#include <fmt/ranges.h>
#endif

using std::cerr;
using std::flush;
using std::ifstream;
using std::make_optional;
using std::make_unique;
using std::max;
using std::min;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::set;
using std::string;
using std::tuple;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
using std::println;
#else
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;
using namespace gcs::test_innards;

namespace
{
    auto fail(const string & message) -> void
    {
        println(cerr, "derived cumulative test failure: {}", message);
        std::exit(EXIT_FAILURE);
    }

    auto constant_value_of(const IntegerVariableID & v) -> Integer
    {
        return std::get<ConstantIntegerVariableID>(v).const_value;
    }

    /**
     * What the demo presolver derives from each Cumulative it finds.
     */
    enum class Demo
    {
        /// C'_t := C_t, copied by a one-line pol. The derived propagator must
        /// then behave exactly like the donor's, which is what makes this the
        /// test of the plumbing rather than of any reasoning.
        Duplicate,
        /// C'_t strengthened by integrality: every height is a multiple of d,
        /// so the load at any time is too, and a capacity that is not gets
        /// rounded down. Uses the subset-sum utility, which takes its
        /// divisibility fast path here.
        Strengthened,
        /// Strengthened, but claiming one unit lower than the derivation
        /// supports. VeriPB must reject.
        ClaimOneLower,
        /// A derived constraint whose tasks run longer than the donor's, so it
        /// asks about (task, time) pairs the donor never encoded. The install
        /// must decline.
        BeyondDonorWindow
    };

    struct DerivedDemoPresolver : Presolver
    {
        Demo demo;
        // Set by run(), read by the test: whether anything was installed.
        std::shared_ptr<bool> installed = std::make_shared<bool>(false);

        explicit DerivedDemoPresolver(Demo d) : demo(d)
        {
        }

        [[nodiscard]] auto run(Problem & problem, Propagators & propagators, State & state, ProofLogger * const logger) -> bool override
        {
            for (const auto & donor : problem.each_constraint_of_type<Cumulative>()) {
                vector<Integer> lengths, heights;
                for (const auto & l : donor.lengths())
                    lengths.push_back(constant_value_of(l));
                for (const auto & h : donor.heights())
                    heights.push_back(constant_value_of(h));
                auto capacity = constant_value_of(donor.capacity());

                // Over the tasks that can raise the profile: a zero height is
                // not a multiple of anything useful, and a task that never
                // loads has no term in the row to divide.
                auto divisor = 0_i;
                for (size_t i = 0; i < heights.size(); ++i)
                    if (lengths[i] > 0_i && heights[i] > 0_i)
                        divisor = Integer{std::gcd(divisor.raw_value, heights[i].raw_value)};

                DerivedCumulativeSpec spec{.donor = donor.constraint_id(),
                    .starts = donor.starts(),
                    .lengths = lengths,
                    .heights = heights,
                    .capacity = capacity,
                    .recipe = {},
                    .rules = CumulativeRules{}};

                switch (demo) {
                case Demo::Duplicate:
                    spec.recipe = [](ProofLogger & logger, ProofLine donor_row, Integer) -> ProofLine {
                        PolBuilder copy;
                        copy.add(donor_row);
                        return copy.emit(logger, ProofLevel::Top);
                    };
                    break;

                case Demo::Strengthened:
                case Demo::ClaimOneLower: {
                    if (divisor <= 1_i)
                        continue; // nothing to round: the derivation would be the duplicate one
                    spec.capacity = divisor * (capacity / divisor);
                    if (demo == Demo::ClaimOneLower)
                        spec.capacity -= 1_i;

                    // The items the donor's row for t is over: one per task
                    // that can be active then, weighted by its height. Looked
                    // up through the same published keys install_derived_-
                    // cumulative uses, which is the presolver's half of the
                    // contract.
                    auto starts = donor.starts();
                    auto donor_id = donor.constraint_id();
                    auto claim_one_lower = (demo == Demo::ClaimOneLower);
                    spec.recipe = [starts, heights, lengths, capacity, donor_id, claim_one_lower, &state](
                                      ProofLogger & logger, ProofLine donor_row, Integer t) -> ProofLine {
                        vector<SubsetSumItem> items;
                        for (size_t i = 0; i < starts.size(); ++i) {
                            if (lengths[i] <= 0_i || heights[i] <= 0_i)
                                continue;
                            auto active = logger.names_and_ids_tracker().find_proof_flag_values(
                                donor_id, ConstraintProofModelData<Cumulative>::active_flag_key(i, t));
                            if (active)
                                items.push_back(SubsetSumItem{heights[i], *active});
                        }

                        auto strengthened = derive_subset_sum_strengthening(logger, items, donor_row, capacity, ProofLevel::Top);
                        if (! claim_one_lower)
                            return strengthened.line;

                        // Claim a capacity the derivation does not support: the
                        // RUP has no way to reach it, so veripb says no.
                        WPBSum load;
                        for (const auto & item : items)
                            load += item.coefficient * std::get<ProofFlag>(item.term);
                        return logger.emit_rup_proof_line(move(load) <= strengthened.bound - 1_i, ProofLevel::Top);
                    };
                } break;

                case Demo::BeyondDonorWindow:
                    // One unit longer than the donor's tasks, so the derived
                    // constraint's last time point is one the donor never
                    // encoded a flag for.
                    for (auto & l : spec.lengths)
                        l += 1_i;
                    spec.recipe = [](ProofLogger & logger, ProofLine donor_row, Integer) -> ProofLine {
                        PolBuilder copy;
                        copy.add(donor_row);
                        return copy.emit(logger, ProofLevel::Top);
                    };
                    break;
                }

                *installed = install_derived_cumulative(propagators, state, logger, move(spec));
            }
            return true;
        }

        [[nodiscard]] auto clone() const -> unique_ptr<Presolver> override
        {
            auto result = make_unique<DerivedDemoPresolver>(demo);
            result->installed = installed;
            return result;
        }
    };

    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<int> lengths;
        vector<int> heights;
        int capacity;
    };

    auto is_satisfying(const Instance & inst, const vector<int> & starts) -> bool
    {
        auto n = inst.start_ranges.size();
        int t_lo = INT_MAX, t_hi = INT_MIN;
        for (size_t i = 0; i < n; ++i) {
            if (inst.lengths[i] == 0 || inst.heights[i] == 0)
                continue;
            t_lo = min(t_lo, starts[i]);
            t_hi = max(t_hi, starts[i] + inst.lengths[i] - 1);
        }
        for (int t = t_lo; t <= t_hi; ++t) {
            int load = 0;
            for (size_t i = 0; i < n; ++i)
                if (starts[i] <= t && t < starts[i] + inst.lengths[i])
                    load += inst.heights[i];
            if (load > inst.capacity)
                return false;
        }
        return true;
    }

    auto post(Problem & p, const Instance & inst, optional<Demo> demo) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}));

        vector<Integer> lengths, heights;
        for (auto l : inst.lengths)
            lengths.push_back(Integer{l});
        for (auto h : inst.heights)
            heights.push_back(Integer{h});

        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}});
        if (demo)
            p.add_presolver(DerivedDemoPresolver{*demo});
        return starts;
    }

    struct Outcome
    {
        set<vector<int>> solutions;
        unsigned long long recursions = 0;
        bool refuted_at_root = false;
    };

    auto solve_it(const Instance & inst, optional<Demo> demo, const optional<string> & proof_name) -> Outcome
    {
        Problem p;
        auto starts = post(p, inst, demo);

        Outcome outcome;
        bool reached_a_node = false, found_a_solution = false;
        auto stats = solve_with(p,
            SolveCallbacks{.solution = [&](const CurrentState & s) -> bool {
                               found_a_solution = true;
                               vector<int> solution;
                               for (const auto & v : starts)
                                   solution.push_back(s(v).raw_value);
                               outcome.solutions.insert(move(solution));
                               return true;
                           },
                .trace = [&](const CurrentState &) -> bool {
                    reached_a_node = true;
                    return true;
                }},
            proof_name ? make_optional<ProofOptions>(ProofFileNames{*proof_name}) : nullopt);

        outcome.recursions = stats.recursions;
        outcome.refuted_at_root = ! reached_a_node && ! found_a_solution;

        if (proof_name)
            verify_proof_and_clean_up(*proof_name);
        return outcome;
    }

    auto read_file(const string & name) -> string
    {
        ifstream in{name, std::ios::binary};
        if (! in)
            fail("could not read " + name);
        return string{std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    }

    // The headline check. A derived constraint's whole reason to exist is that
    // a presolver can add an implied constraint without touching the model:
    // the OPB is the statement being verified, so a presolver that wrote into
    // it would be changing the statement rather than proving anything about it,
    // and every proof in this file would verify and mean nothing.
    auto check_opb_unaffected(const string & what, const Instance & inst, Demo demo) -> void
    {
        const string with = "derived_cumulative_opb_with", without = "derived_cumulative_opb_without";

        // A trace callback that stops at once: the model is written before the
        // search, and this is about the model.
        auto write_model_only = [&](const string & name, optional<Demo> d) {
            Problem p;
            post(p, inst, d);
            solve_with(
                p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }}, make_optional<ProofOptions>(ProofFileNames{name}));
        };

        write_model_only(with, make_optional(demo));
        write_model_only(without, nullopt);

        if (read_file(with + ".opb") != read_file(without + ".opb"))
            fail("the derived constraint changed the OPB, on " + what);

        for (const auto & name : {with, without})
            dispose_of_proof_files(name);
    }
}

auto main(int argc, char * argv[]) -> int
{
    establish_and_announce_seed(argc, argv);
    auto proofs = can_run_veripb();

    // Demo one: a verbatim duplicate. Two tasks that cannot overlap under a
    // capacity of one, so there is real propagation to compare.
    const Instance duplicate_instance{{{0, 4}, {0, 4}, {0, 4}}, {2, 2, 3}, {1, 1, 1}, 1};

    {
        auto donor_only = solve_it(duplicate_instance, nullopt, nullopt);
        auto with_derived =
            solve_it(duplicate_instance, make_optional(Demo::Duplicate), proofs ? make_optional("derived_cumulative_duplicate") : nullopt);

        if (donor_only.solutions != with_derived.solutions)
            fail("duplicate demo: the solution set changed");
        if (donor_only.recursions != with_derived.recursions)
            fail("duplicate demo: the search changed, so the copy is not behaving like the donor (" + std::to_string(donor_only.recursions) +
                " nodes against " + std::to_string(with_derived.recursions) + ")");

        set<vector<int>> expected;
        build_expected(
            expected, [&](const vector<int> & starts) { return is_satisfying(duplicate_instance, starts); }, duplicate_instance.start_ranges);
        if (expected != with_derived.solutions)
            fail("duplicate demo: solutions do not match brute force");
    }

    // Demo two: strengthening by integrality. Every height is a multiple of
    // three, so the load at any time is a multiple of three, and a capacity of
    // eight is really a capacity of six.
    //
    // That difference is invisible to time-tabling --- a load is a sum of
    // heights, so it clears eight exactly when it clears six --- and shows up
    // only in the energy argument, where the window's supply is capacity times
    // its width and *that* is not a multiple of three. Seven unit-length tasks
    // of height three need 21 units of energy in [0, 3), which a capacity of
    // eight supplies (24) and a capacity of six does not (18). So the donor
    // alone has nothing to say at the root, and the derived constraint refutes
    // it there.
    const Instance strengthened_instance{{{0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}, {0, 2}}, {1, 1, 1, 1, 1, 1, 1}, {3, 3, 3, 3, 3, 3, 3}, 8};

    {
        auto donor_only = solve_it(strengthened_instance, nullopt, nullopt);
        if (donor_only.refuted_at_root)
            fail("strengthened demo: the donor alone refuted at the root, so the fixture proves nothing");

        auto with_derived =
            solve_it(strengthened_instance, make_optional(Demo::Strengthened), proofs ? make_optional("derived_cumulative_strengthened") : nullopt);
        if (! with_derived.refuted_at_root)
            fail("strengthened demo: the derived constraint did not refute at the root");
        if (! with_derived.solutions.empty())
            fail("strengthened demo: the instance is unsatisfiable but solutions were reported");
    }

    // Nothing above may have reached the OPB.
    check_opb_unaffected("duplicate", duplicate_instance, Demo::Duplicate);
    check_opb_unaffected("strengthened", strengthened_instance, Demo::Strengthened);

    // A derived constraint is implied, so it must not cost solutions. Random
    // instances, against brute force, with the duplicate recipe (which keeps
    // the propagation identical) and the strengthening one (which does not).
    {
        std::mt19937 rand(*get_seed());
        std::uniform_int_distribution<> n_dist(2, 3), lo_dist(0, 3), span_dist(0, 3), len_dist(0, 3), ht_dist(0, 2), cap_dist(1, 4);

        for (int k = 0; k < 60; ++k) {
            Instance inst;
            auto n = n_dist(rand);
            for (int i = 0; i < n; ++i) {
                auto lo = lo_dist(rand), span = span_dist(rand);
                inst.start_ranges.emplace_back(lo, lo + span);
                inst.lengths.push_back(len_dist(rand));
                // Heights in multiples of two, so the strengthening has
                // something to round.
                inst.heights.push_back(2 * ht_dist(rand));
            }
            inst.capacity = cap_dist(rand);

            set<vector<int>> expected;
            build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(inst, starts); }, inst.start_ranges);

            for (auto demo : {Demo::Duplicate, Demo::Strengthened}) {
                auto outcome = solve_it(inst, make_optional(demo), nullopt);
                if (outcome.solutions != expected) {
                    println(cerr, "starts={} lens={} hts={} c={}", inst.start_ranges, inst.lengths, inst.heights, inst.capacity);
                    fail("a derived constraint removed solutions");
                }
            }
        }
    }

    // A derived constraint that asks about a (task, time) the donor never
    // encoded must be declined, not guessed at.
    {
        Problem p;
        post(p, duplicate_instance, make_optional(Demo::BeyondDonorWindow));
        // The presolver's own record of what happened: with proofs on there is
        // nothing to cite past the donor's window, so nothing is installed.
        auto presolver = DerivedDemoPresolver{Demo::BeyondDonorWindow};
        auto installed = presolver.installed;
        Problem p2;
        auto starts = post(p2, duplicate_instance, nullopt);
        p2.add_presolver(presolver);
        solve_with(p2, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return false; }},
            proofs ? make_optional<ProofOptions>(ProofFileNames{"derived_cumulative_beyond_window"}) : nullopt);
        if (proofs) {
            if (*installed)
                fail("a derived constraint reaching past the donor's windows was installed anyway");
            dispose_of_proof_files("derived_cumulative_beyond_window");
        }
    }

    if (! proofs) {
        println(cerr, "veripb is not available, so the proof-level checks are skipped");
        return EXIT_SUCCESS;
    }

    // Claiming a capacity the derivation does not support must be rejected.
    {
        Problem p;
        post(p, strengthened_instance, make_optional(Demo::ClaimOneLower));
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }},
            make_optional<ProofOptions>(ProofFileNames{"derived_cumulative_one_lower"}));

        if (run_veripb("derived_cumulative_one_lower.opb", "derived_cumulative_one_lower.pbp"))
            fail("veripb accepted a derived capacity one lower than the derivation supports");
        println(cerr, "veripb rejected the one-lower capacity, as expected");
        dispose_of_proof_files("derived_cumulative_one_lower");
    }

    // Backtracking soak: the derived rows are emitted once, at the top of the
    // proof, and cited at every node. A search that backtracks deeply would
    // find them gone if they had been emitted at any other level.
    {
        const Instance soak{{{0, 5}, {0, 5}, {0, 5}, {0, 5}}, {2, 2, 3, 3}, {2, 2, 2, 4}, 6};
        auto outcome = solve_it(soak, make_optional(Demo::Strengthened), make_optional("derived_cumulative_soak"));
        println(cerr, "backtracking soak: {} solutions over {} nodes", outcome.solutions.size(), outcome.recursions);
        if (outcome.recursions < 5)
            fail("backtracking soak: the instance did not search, so it soaked nothing");

        set<vector<int>> expected;
        build_expected(expected, [&](const vector<int> & starts) { return is_satisfying(soak, starts); }, soak.start_ranges);
        if (expected != outcome.solutions)
            fail("backtracking soak: solutions do not match brute force");
    }

    return EXIT_SUCCESS;
}
