#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/innards/constraints_test_utils.hh>
#include <gcs/constraints/linear.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/subset_sum_strengthening.hh>
#include <gcs/presolver.hh>
#include <gcs/presolvers/innards/makespan_links.hh>
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
        BeyondDonorWindow,
        /// C'_t := C_t, plus a certified lower bound on the makespan from the
        /// tasks' energy.
        Makespan,
        /// The same, claiming a makespan one larger than the energy supports.
        /// VeriPB must reject.
        MakespanClaimHigher,
        /// The same, counting the window one capacity row short. VeriPB must
        /// reject.
        MakespanOmitRow,
        /// The same, deriving the tasks' window energy without the deadline
        /// that confines them to the window. VeriPB must reject.
        MakespanForgetDeadline
    };

    struct DerivedDemoPresolver : Presolver
    {
        Demo demo;
        // The model's makespan variable, for the demos that bound it.
        optional<IntegerVariableID> makespan;
        // Set by run(), read by the test: whether anything was installed.
        std::shared_ptr<bool> installed = std::make_shared<bool>(false);
        // Set by the derived constraint's initialiser: the bound it reached.
        std::shared_ptr<optional<Integer>> bound_reached = std::make_shared<optional<Integer>>();

        explicit DerivedDemoPresolver(Demo d, optional<IntegerVariableID> m = nullopt) : demo(d), makespan(m)
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

                auto donor_id = donor.constraint_id();
                DerivedCumulativeSpec spec{.tasks = derived_cumulative_tasks_from(donor_id, donor.starts(), lengths, heights),
                    .capacity = capacity,
                    .row_donors = {donor_id},
                    .recipe = {},
                    .rules = CumulativeRules{}};

                // Every demo here derives from the one donor it was built over,
                // so each pulls that donor's row out of the map it is handed.
                auto row_of = [donor_id](const DerivedCumulativeRows & rows) -> ProofLine {
                    auto at = rows.find(donor_id);
                    if (at == rows.end())
                        fail("the donor had no capacity row where the derived constraint has one");
                    return at->second;
                };

                switch (demo) {
                case Demo::Duplicate:
                    spec.recipe = [row_of](ProofLogger & logger, const DerivedCumulativeRows & rows, Integer) -> optional<ProofLine> {
                        PolBuilder copy;
                        copy.add(row_of(rows));
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
                    auto claim_one_lower = (demo == Demo::ClaimOneLower);
                    spec.recipe = [starts, heights, lengths, capacity, donor_id, claim_one_lower, row_of, &state](
                                      ProofLogger & logger, const DerivedCumulativeRows & rows, Integer t) -> optional<ProofLine> {
                        auto donor_row = row_of(rows);
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

                case Demo::Makespan:
                case Demo::MakespanClaimHigher:
                case Demo::MakespanOmitRow:
                case Demo::MakespanForgetDeadline:
                    if (! makespan)
                        fail("a makespan demo was run on a model with no makespan variable");
                    spec.makespan = makespan;
                    {
                        // What the model says the makespan is: the rows the
                        // derivation sums, rather than a promise it makes.
                        auto links = find_makespan_links(problem, logger, *makespan);
                        for (const auto & task : spec.tasks) {
                            auto link = links.find(task.start);
                            spec.makespan_links.push_back(link == links.end() ? nullopt : make_optional<makespan_energy::MakespanLink>(link->second));
                        }
                    }
                    spec.makespan_bound_reached = [reached = bound_reached](Integer bound) { *reached = bound; };
                    switch (demo) {
                    case Demo::MakespanClaimHigher: spec.makespan_mutation = makespan_energy::makespan_energy_mutation::ClaimHigherBound{}; break;
                    case Demo::MakespanOmitRow: spec.makespan_mutation = makespan_energy::makespan_energy_mutation::OmitCapacityRow{}; break;
                    case Demo::MakespanForgetDeadline: spec.makespan_mutation = makespan_energy::makespan_energy_mutation::ForgetTheDeadline{}; break;
                    default: break;
                    }
                    spec.recipe = [row_of](ProofLogger & logger, const DerivedCumulativeRows & rows, Integer) -> optional<ProofLine> {
                        PolBuilder copy;
                        copy.add(row_of(rows));
                        return copy.emit(logger, ProofLevel::Top);
                    };
                    break;

                case Demo::BeyondDonorWindow:
                    // One unit longer than the donor's tasks, so the derived
                    // constraint's last time point is one the donor never
                    // encoded a flag for.
                    for (auto & task : spec.tasks)
                        task.length += 1_i;
                    spec.recipe = [row_of](ProofLogger & logger, const DerivedCumulativeRows & rows, Integer) -> optional<ProofLine> {
                        PolBuilder copy;
                        copy.add(row_of(rows));
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
            auto result = make_unique<DerivedDemoPresolver>(demo, makespan);
            result->installed = installed;
            result->bound_reached = bound_reached;
            return result;
        }
    };

    struct Instance
    {
        vector<pair<int, int>> start_ranges;
        vector<int> lengths;
        vector<int> heights;
        int capacity;
        /// When set, the model also gets a `makespan` variable over
        /// `[0, horizon]` with `start_i + length_i <= makespan` for every task
        /// --- which is the entailment the makespan bound's derivation rests
        /// on, and the only thing that makes those demos legal.
        optional<int> makespan_horizon = nullopt;
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

    struct Posted
    {
        vector<IntegerVariableID> starts;
        optional<IntegerVariableID> makespan;
        /// The demo presolver's record of what its derived constraint's
        /// initialiser inferred, if anything.
        std::shared_ptr<optional<Integer>> bound_reached;
    };

    auto post(Problem & p, const Instance & inst, optional<Demo> demo, CumulativeRules donor_rules = CumulativeRules{}) -> Posted
    {
        vector<IntegerVariableID> starts;
        for (auto & [lo, hi] : inst.start_ranges)
            starts.push_back(p.create_integer_variable(Integer{lo}, Integer{hi}, "start" + std::to_string(starts.size())));

        vector<Integer> lengths, heights;
        for (auto l : inst.lengths)
            lengths.push_back(Integer{l});
        for (auto h : inst.heights)
            heights.push_back(Integer{h});

        optional<IntegerVariableID> makespan;
        if (inst.makespan_horizon) {
            makespan = p.create_integer_variable(0_i, Integer{*inst.makespan_horizon}, "makespan");
            for (size_t i = 0; i < starts.size(); ++i)
                p.post(LinearGreaterThanEqual{WeightedSum{} + 1_i * *makespan + -1_i * starts[i], lengths[i]});
        }

        p.post(Cumulative{starts, lengths, heights, Integer{inst.capacity}}.with_rules(donor_rules));
        auto presolver = DerivedDemoPresolver{demo.value_or(Demo::Duplicate), makespan};
        if (demo)
            p.add_presolver(presolver);
        return Posted{move(starts), makespan, presolver.bound_reached};
    }

    struct Outcome
    {
        set<vector<int>> solutions;
        unsigned long long recursions = 0;
        bool refuted_at_root = false;
        /// What the makespan demos' initialiser inferred, if it ran.
        optional<Integer> makespan_bound;
    };

    auto solve_it(const Instance & inst, optional<Demo> demo, const optional<string> & proof_name, CumulativeRules donor_rules = CumulativeRules{})
        -> Outcome
    {
        Problem p;
        auto posted = post(p, inst, demo, donor_rules);
        const auto & starts = posted.starts;

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
        outcome.makespan_bound = *posted.bound_reached;

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

    // The derived propagator has to be the one doing the work, not a
    // bystander watching the donor do it. With the donor's own rules turned off
    // it infers nothing at all, so every inference in this solve --- and every
    // justification --- comes from the derived constraint, over the donor's
    // flags and its own derived rows.
    {
        const CumulativeRules silent{.time_table = false, .overload = false, .profile_overload = false};

        auto donor_silent = solve_it(duplicate_instance, nullopt, nullopt, silent);
        auto derived_working =
            solve_it(duplicate_instance, make_optional(Demo::Duplicate), proofs ? make_optional("derived_cumulative_carrying") : nullopt, silent);

        set<vector<int>> expected;
        build_expected(
            expected, [&](const vector<int> & starts) { return is_satisfying(duplicate_instance, starts); }, duplicate_instance.start_ranges);
        if (derived_working.solutions != expected)
            fail("carrying demo: solutions do not match brute force with the donor silent");
        if (derived_working.recursions >= donor_silent.recursions)
            fail("carrying demo: the derived constraint pruned nothing (" + std::to_string(derived_working.recursions) + " nodes against " +
                std::to_string(donor_silent.recursions) + " with nothing propagating), so its proof path is untested");
        println(cerr, "derived propagator carrying alone: {} nodes against {} with nothing propagating", derived_working.recursions,
            donor_silent.recursions);
    }

    // Demo three: a certified makespan bound. Three tasks of length two on a
    // unary resource must run one after another, so no schedule finishes before
    // time six --- and the makespan variable's own domain, and the model's
    // `start + 2 <= makespan` rows, say only that it is at least two.
    //
    // The margin is exactly one: over [0, 5) the tasks need six units and the
    // resource supplies five. That is what makes the mutations below bite; with
    // any slack a corrupted derivation lands somewhere weaker and still
    // contradicts.
    const Instance makespan_instance{{{0, 5}, {0, 5}, {0, 5}}, {2, 2, 2}, {1, 1, 1}, 1, make_optional(8)};

    {
        auto with_bound = solve_it(makespan_instance, make_optional(Demo::Makespan), proofs ? make_optional("derived_cumulative_makespan") : nullopt);

        if (with_bound.makespan_bound != make_optional(6_i))
            fail("makespan demo: the derived constraint inferred " +
                (with_bound.makespan_bound ? std::to_string(with_bound.makespan_bound->raw_value) : string{"nothing"}) +
                ", not the six its tasks' energy supports");

        set<vector<int>> expected;
        build_expected(
            expected, [&](const vector<int> & starts) { return is_satisfying(makespan_instance, starts); }, makespan_instance.start_ranges);
        if (expected != with_bound.solutions)
            fail("makespan demo: solutions do not match brute force");

        // With proofs off the bound has to be the same number, or the solver is
        // doing different arithmetic depending on whether anyone is watching.
        auto unproved = solve_it(makespan_instance, make_optional(Demo::Makespan), nullopt);
        if (unproved.makespan_bound != with_bound.makespan_bound)
            fail("makespan demo: the bound differs with proofs off");
    }

    // Nothing above may have reached the OPB.
    check_opb_unaffected("duplicate", duplicate_instance, Demo::Duplicate);
    check_opb_unaffected("strengthened", strengthened_instance, Demo::Strengthened);
    check_opb_unaffected("makespan", makespan_instance, Demo::Makespan);

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
        post(p2, duplicate_instance, nullopt);
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

    // Each way of getting the makespan bound wrong, and VeriPB refusing it.
    // The `+1` is the one that matters: a bound whose derivation has slack
    // verifies whatever it concludes, so only a refusal says this one is tight.
    for (auto [demo, what] : {pair{Demo::MakespanClaimHigher, "a makespan one larger than the energy supports"},
             pair{Demo::MakespanOmitRow, "a makespan bound counting the window one capacity row short"},
             pair{Demo::MakespanForgetDeadline, "a makespan bound whose window energy forgets the deadline"}}) {
        const string name = "derived_cumulative_makespan_mutation";
        Problem p;
        post(p, makespan_instance, make_optional(demo));
        solve_with(p, SolveCallbacks{.trace = [](const CurrentState &) -> bool { return true; }}, make_optional<ProofOptions>(ProofFileNames{name}));

        if (run_veripb(name + ".opb", name + ".pbp"))
            fail(string{"veripb accepted "} + what);
        println(cerr, "veripb rejected {}, as expected", what);
        dispose_of_proof_files(name);
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
