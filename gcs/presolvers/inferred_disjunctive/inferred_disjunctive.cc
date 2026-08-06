#include <gcs/constraint_id.hh>
#include <gcs/constraints/cumulative.hh>
#include <gcs/constraints/cumulative/derived_cumulative.hh>
#include <gcs/constraints/cumulative/donor_view.hh>
#include <gcs/constraints/cumulative/propagate.hh>
#include <gcs/exception.hh>
#include <gcs/innards/proofs/am1_from_pairs.hh>
#include <gcs/innards/proofs/am1_from_row.hh>
#include <gcs/innards/proofs/flag_bridge.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/pol_builder.hh>
#include <gcs/innards/proofs/proof_error.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_scaffolding_scope.hh>
#include <gcs/innards/proofs/pseudo_boolean.hh>
#include <gcs/innards/state.hh>
#include <gcs/presolvers/inferred_disjunctive/inferred_disjunctive.hh>
#include <gcs/presolvers/innards/makespan_links.hh>
#include <gcs/problem.hh>

#include <algorithm>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_unique;
using std::map;
using std::move;
using std::optional;
using std::pair;
using std::set;
using std::shared_ptr;
using std::size_t;
using std::to_string;
using std::unique_ptr;
using std::vector;

namespace
{
    /// One appearance of a task on a resource: which donor, where in it, and
    /// what it demands there.
    struct Appearance
    {
        ConstraintID donor;
        size_t position;
        Integer height;
    };

    /// A task, as the conflict graph sees it. Identified by its start variable,
    /// which is what makes two donors' entries the same task.
    struct Task
    {
        IntegerVariableID start;
        /// As posted, which may be a variable: it is what the derived
        /// constraint is given, so that its propagator reads the same duration
        /// the donor's flags were reified on.
        IntegerVariableID length;
        /// The duration this task is guaranteed to occupy, lb(length). What a
        /// clique can *say* about the schedule is a statement about durations
        /// every solution has to contain, so it is the smallest one still
        /// allowed that every energy sum and every ranking here counts.
        Integer least_length;
        Integer t_lo, t_hi;
        vector<Appearance> appearances;
    };

    /// A resource, once confirmed usable.
    struct Resource
    {
        ConstraintID id;
        Integer capacity;
        /// How many tasks it was posted over, which is how far a weakening
        /// sweep has to go: positions with no flags are simply skipped.
        size_t size;
    };

    /// The witness resources' views, by donor, as a recipe needs them: to
    /// reduce a row to the constant-argument form build_am1_from_row reads, and
    /// to know which of that resource's positions still have a term in it.
    using DonorViews = map<ConstraintID, CumulativeDonorView>;

    /// Why a pair conflicts: the resource that cannot hold both, and the
    /// numbers saying it cannot. The demands and the capacity rather than the
    /// margin between them, because that is what recovering the at-most-one
    /// needs, and a caller that works the margin out for itself is a caller
    /// that can work it out wrongly.
    struct Conflict
    {
        ConstraintID witness;
        size_t witness_position_u, witness_position_v;
        Integer demand_u, demand_v, capacity;
    };

    /// The flags a task's activity is expressed in, on one resource, at one
    /// time. Absent when that resource never encoded the pair.
    [[nodiscard]] auto flags_for(const NamesAndIDsTracker & tracker, const ConstraintID & donor, size_t position, Integer t)
        -> optional<std::tuple<ProofFlag, ProofFlag, ProofFlag>>
    {
        auto before = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::before_flag_key(position, t));
        auto after = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::after_flag_key(position, t));
        auto active = tracker.find_proof_flag_values(donor, ConstraintProofModelData<Cumulative>::active_flag_key(position, t));
        if (! before || ! after || ! active)
            return std::nullopt;
        return std::tuple{*before, *after, *active};
    }
}

InferredDisjunctive::InferredDisjunctive(shared_ptr<InferredDisjunctiveStats> stats) :
    _stats(move(stats)), _max_candidates(100), _max_posted(5), _min_clique_size(3),
    // Energy only: a conflicting pair is already kept apart by the resource
    // that witnesses it, so an inferred constraint's time-tabling is redundant.
    _rules(CumulativeRules{.time_table = false, .overload = true, .profile_overload = true}), _mutation(inferred_disjunctive_mutation::None{})
{
}

auto InferredDisjunctive::with_makespan(IntegerVariableID makespan) -> InferredDisjunctive &
{
    _makespan = makespan;
    return *this;
}

auto InferredDisjunctive::with_proof_mutation(InferredDisjunctiveMutation mutation) -> InferredDisjunctive &
{
    _mutation = mutation;
    return *this;
}

auto InferredDisjunctive::with_budgets(size_t max_candidates, size_t max_posted) -> InferredDisjunctive &
{
    _max_candidates = max_candidates;
    _max_posted = max_posted;
    return *this;
}

auto InferredDisjunctive::with_minimum_clique_size(size_t size) -> InferredDisjunctive &
{
    _min_clique_size = size;
    return *this;
}

auto InferredDisjunctive::with_rules(CumulativeRules rules) -> InferredDisjunctive &
{
    _rules = rules;
    return *this;
}

auto InferredDisjunctive::run(Problem & problem, Propagators & propagators, State & state, ProofLogger * const logger) -> bool
{
    auto bump = [&](size_t InferredDisjunctiveStats::* field, size_t by = 1) {
        if (_stats)
            (*_stats).*field += by;
    };

    // What the model says about the makespan, if the caller named one: the rows
    // saying each task finishes by it, which are what a bound on it is derived
    // from. Looked up once rather than per clique.
    map<IntegerVariableID, makespan_energy::MakespanLink> makespan_links;
    if (_makespan)
        makespan_links = find_makespan_links(problem, logger, *_makespan);

    auto claim_rhs_zero = std::holds_alternative<inferred_disjunctive_mutation::ClaimRhsZero>(_mutation);
    auto bridge_wrong_task = std::holds_alternative<inferred_disjunctive_mutation::BridgeWrongTask>(_mutation);
    auto include_non_conflicting = std::holds_alternative<inferred_disjunctive_mutation::IncludeNonConflicting>(_mutation);

    // Collect the tasks, keyed by start variable so that the same task on two
    // resources is one node of the conflict graph.
    vector<Task> tasks;
    map<IntegerVariableID, size_t> task_of_start;
    vector<Resource> resources;
    DonorViews views;

    for (const auto & donor : problem.each_constraint_of_type<Cumulative>()) {
        bump(&InferredDisjunctiveStats::donors_seen);

        // The mechanism no longer minds an optional donor --- a presence is a
        // conjunct of the activity flag, so the rows this argues over are the
        // same shape, and install_derived_cumulative carries the literal into
        // the reasons. What is still open here is the *cross-donor* half: this
        // presolver draws tasks from several Cumulatives and bridges one
        // donor's flags to another's, and two donors' activity flags cancel
        // against each other only if their presence conjuncts do too. Declined
        // until that has a rule of its own rather than a hopeful `pol`.
        if (! donor.presences().empty()) {
            bump(&InferredDisjunctiveStats::declined_optional);
            if (logger)
                logger->emit_proof_comment("presolve disjunctive: declining " + as_string(donor.constraint_id()) + ", optional tasks");
            continue;
        }

        // What of this donor an inferred constraint can argue over: its
        // capacity as a number, and the tasks whose height is the constant its
        // rows put on them. A task with a variable one is set aside rather than
        // costing the whole resource its place in the conflict graph --- it
        // simply cannot be a clique member, and every row this resource
        // witnesses is weakened over it first. A variable duration is no
        // obstacle: a conflict is a statement about heights, and a clique's
        // rows say nothing about how long anything runs for.
        auto view = cumulative_donor_view(donor, state, logger);
        if (! view) {
            bump(&InferredDisjunctiveStats::declined_irreducible_capacity);
            if (logger)
                logger->emit_proof_comment("presolve disjunctive: declining " + as_string(donor.constraint_id()) + ", capacity is not reducible");
            continue;
        }
        if (! view->set_aside.empty())
            bump(&InferredDisjunctiveStats::resources_with_set_aside_tasks);
        for (auto i : view->usable)
            if (view->height_bounded_by[i])
                bump(&InferredDisjunctiveStats::converted_heights);

        const auto & starts = donor.starts();
        resources.push_back(Resource{donor.constraint_id(), view->capacity, starts.size()});
        const auto & lengths = view->lengths;
        const auto & heights = view->heights;
        views.emplace(donor.constraint_id(), *view);

        for (auto i : view->usable) {
            auto found = task_of_start.find(starts[i]);
            if (found == task_of_start.end()) {
                auto window = cumulative_task_window(state, starts[i], lengths[i]);
                found = task_of_start.emplace(starts[i], tasks.size()).first;
                tasks.push_back(Task{starts[i], lengths[i], state.lower_bound(lengths[i]), window.lo, window.hi, {}});
            }
            else if (tasks[found->second].length != lengths[i]) {
                // Two resources disagreeing about a duration is not something
                // to average over: the flags would reify different conditions
                // and no bridge between them exists. The same variable is the
                // same duration, whatever its bounds come to; two different
                // ones are not, even where their bounds agree today.
                continue;
            }

            tasks[found->second].appearances.push_back(Appearance{donor.constraint_id(), i, heights[i]});
        }
    }

    bump(&InferredDisjunctiveStats::tasks, tasks.size());
    if (tasks.size() < _min_clique_size)
        return true;

    // The conflict graph. A pair conflicts if some one resource cannot hold
    // both; the first such resource found is the witness the certificate will
    // use, since any of them proves the same at-most-one.
    map<ConstraintID, Integer> capacity_of;
    for (const auto & resource : resources)
        capacity_of.emplace(resource.id, resource.capacity);

    vector<vector<optional<Conflict>>> conflict(tasks.size(), vector<optional<Conflict>>(tasks.size()));
    vector<pair<size_t, size_t>> candidate_pairs;
    for (size_t u = 0; u < tasks.size(); ++u)
        for (size_t v = u + 1; v < tasks.size(); ++v) {
            for (const auto & au : tasks[u].appearances) {
                for (const auto & av : tasks[v].appearances) {
                    if (au.donor != av.donor)
                        continue;
                    auto capacity = capacity_of.at(au.donor);
                    if (au.height + av.height <= capacity)
                        continue;
                    conflict[u][v] = conflict[v][u] = Conflict{au.donor, au.position, av.position, au.height, av.height, capacity};
                    break;
                }
                if (conflict[u][v])
                    break;
            }

            if (conflict[u][v]) {
                bump(&InferredDisjunctiveStats::conflicting_pairs);
                candidate_pairs.emplace_back(u, v);
            }
        }

    if (candidate_pairs.empty())
        return true;

    // Grow each candidate pair into a maximal clique, taking the longest task
    // first --- the unit-coefficient reading of Sidorov's lifting order, and
    // the one that maximises the energy the resulting constraint can argue
    // about.
    auto grow = [&](size_t u, size_t v) -> vector<size_t> {
        vector<size_t> clique{u, v};
        vector<size_t> candidates;
        for (size_t w = 0; w < tasks.size(); ++w)
            if (w != u && w != v && conflict[u][w] && conflict[v][w])
                candidates.push_back(w);

        std::sort(candidates.begin(), candidates.end(), [&](size_t a, size_t b) {
            if (tasks[a].least_length != tasks[b].least_length)
                return tasks[a].least_length > tasks[b].least_length;
            return a < b;
        });

        for (auto w : candidates) {
            bool joins = true;
            for (auto member : clique)
                if (! conflict[member][w]) {
                    joins = false;
                    break;
                }
            if (joins)
                clique.push_back(w);
        }

        std::sort(clique.begin(), clique.end());
        return clique;
    };

    vector<vector<size_t>> found;
    set<vector<size_t>> seen;
    size_t considered = 0;
    for (const auto & [u, v] : candidate_pairs) {
        if (considered >= _max_candidates) {
            bump(&InferredDisjunctiveStats::dropped_over_budget, candidate_pairs.size() - considered);
            if (logger)
                logger->emit_proof_comment("presolve disjunctive: " + to_string(candidate_pairs.size() - considered) +
                    " candidate pairs left ungrown, against a budget of " + to_string(_max_candidates));
            break;
        }
        ++considered;

        auto clique = grow(u, v);
        if (clique.size() < _min_clique_size) {
            bump(&InferredDisjunctiveStats::dropped_too_small);
            continue;
        }
        if (! seen.insert(clique).second)
            continue;
        found.push_back(move(clique));
    }

    // The camouflage mutation: extend one clique with a task that is
    // *compatible* with its members, inventing the conflict record the
    // certificate would need. A pair whose demands sum to exactly the capacity
    // looks like a conflict to an off-by-one and is not one, and the
    // at-most-one for it cannot be derived --- which is what has to be caught.
    if (include_non_conflicting && ! found.empty()) {
        auto & clique = found.front();
        for (size_t w = 0; w < tasks.size(); ++w) {
            if (std::find(clique.begin(), clique.end(), w) != clique.end())
                continue;

            // Every member has to at least share a resource with it, or there
            // would be no row to build a bogus at-most-one on.
            vector<pair<size_t, Conflict>> invented;
            bool usable = true;
            for (auto member : clique) {
                if (conflict[member][w]) {
                    invented.emplace_back(member, *conflict[member][w]);
                    continue;
                }
                optional<Conflict> shared;
                for (const auto & aw : tasks[w].appearances)
                    for (const auto & am : tasks[member].appearances)
                        if (aw.donor == am.donor && ! shared)
                            // Demands that overshoot by exactly one: a lie,
                            // and the same lie the mutation is about, since
                            // what it fabricates is a conflict that is not
                            // there. Recovering the at-most-one then runs
                            // honestly on numbers that are wrong.
                            shared = Conflict{aw.donor, am.position, aw.position, capacity_of.at(aw.donor), 1_i, capacity_of.at(aw.donor)};
                if (! shared) {
                    usable = false;
                    break;
                }
                invented.emplace_back(member, *shared);
            }
            if (! usable)
                continue;

            for (const auto & [member, c] : invented)
                if (! conflict[member][w]) {
                    conflict[member][w] = c;
                    conflict[w][member] = Conflict{c.witness, c.witness_position_v, c.witness_position_u, c.demand_v, c.demand_u, c.capacity};
                }
            clique.push_back(w);
            std::sort(clique.begin(), clique.end());
            break;
        }
    }

    bump(&InferredDisjunctiveStats::cliques_found, found.size());

    // The capacity bound a clique carries: its members run one after another, so
    // the schedule cannot finish before their durations summed. This is
    // Sidorov's L at unit coefficients, it is what the cliques are ranked by,
    // and it is what InferredDisjunctiveStats reports --- one function, so the
    // number a test compares against a published bound is the number the
    // ranking actually used.
    auto capacity_bound = [&](const vector<size_t> & c) {
        auto sum = 0_i;
        for (auto i : c)
            sum += tasks[i].least_length;
        return sum;
    };

    // Rank by that, and drop any clique contained in one already accepted.
    std::sort(found.begin(), found.end(), [&](const vector<size_t> & a, const vector<size_t> & b) {
        auto ta = capacity_bound(a), tb = capacity_bound(b);
        if (ta != tb)
            return ta > tb;
        return a < b;
    });

    vector<vector<size_t>> accepted;
    for (auto & clique : found) {
        if (accepted.size() >= _max_posted) {
            bump(&InferredDisjunctiveStats::dropped_over_budget);
            if (logger)
                logger->emit_proof_comment("presolve disjunctive: a clique beyond the output budget of " + to_string(_max_posted) + " was dropped");
            continue;
        }

        bool subsumed = false;
        for (const auto & already : accepted)
            if (std::includes(already.begin(), already.end(), clique.begin(), clique.end())) {
                subsumed = true;
                break;
            }
        if (subsumed) {
            bump(&InferredDisjunctiveStats::dropped_subset);
            continue;
        }

        accepted.push_back(move(clique));
    }

    for (const auto & clique : accepted) {
        // Each member's flags come from its first appearance; the certificate
        // bridges a pair's witness across to those where they differ.
        vector<DerivedCumulativeTask> derived_tasks;
        vector<optional<makespan_energy::MakespanLink>> links;
        set<ConstraintID> row_donors;
        for (auto i : clique) {
            const auto & home = tasks[i].appearances.front();
            auto link = makespan_links.find(tasks[i].start);
            links.push_back(link == makespan_links.end() ? std::nullopt : optional<makespan_energy::MakespanLink>{link->second});
            derived_tasks.push_back(DerivedCumulativeTask{home.donor, home.position, tasks[i].start, tasks[i].length, 1_i});
        }
        for (size_t a = 0; a < clique.size(); ++a)
            for (size_t b = a + 1; b < clique.size(); ++b)
                row_donors.insert(conflict[clique[a]][clique[b]]->witness);

        auto members = clique;
        auto task_data = tasks;
        auto conflicts = conflict;
        auto stats = _stats;

        DerivedCumulativeSpec spec{.tasks = derived_tasks,
            .capacity = 1_i,
            .row_donors = vector<ConstraintID>{row_donors.begin(), row_donors.end()},
            .recipe = [members, task_data, conflicts, views, stats, claim_rhs_zero, bridge_wrong_task](
                          ProofLogger & recipe_logger, const DerivedCumulativeRows & rows, Integer t) -> optional<ProofLine> {
                auto & tracker = recipe_logger.names_and_ids_tracker();

                // Only the members that can be running at t appear in this time
                // point's inequality; the donors windowed them all the same way,
                // so this is the same set their flags exist for.
                vector<size_t> here;
                for (auto i : members)
                    if (t >= task_data[i].t_lo && t <= task_data[i].t_hi)
                        here.push_back(i);

                vector<ProofLiteralOrFlag> flags;
                for (auto i : here) {
                    const auto & home = task_data[i].appearances.front();
                    auto found = flags_for(tracker, home.donor, home.position, t);
                    if (! found)
                        return std::nullopt;
                    flags.push_back(std::get<2>(*found));
                }

                WPBSum at_most_one;
                for (const auto & flag : flags)
                    add_term_to(at_most_one, 1_i, flag);

                // One member here means the row says a single flag is at most
                // one, which is true of any 0/1 and needs no derivation.
                if (here.size() < 2)
                    return recipe_logger.emit_rup_proof_line(move(at_most_one) <= 1_i, ProofLevel::Top);

                recipe_logger.emit_proof_comment("presolve disjunctive clique at time " + to_string(t.raw_value));

                // The bridges and the pairwise at-most-ones go one proof level
                // deeper than the caller's and are forgotten on the way out.
                // They exist only to reach the line recover_am1_from_pairs pins,
                // and at Top there are order k squared of them per time point,
                // none of which is ever deleted -- 180k live constraints from
                // one presolver on a realistic instance, taxing every later
                // unhinted RUP (issue #666).
                ProofScaffoldingScope scaffolding{recipe_logger};

                // Bridges, once per (member, witnessing resource) rather than
                // once per pair: several pairs of a clique often share a witness.
                map<pair<size_t, ConstraintID>, ProofLine> bridges;
                auto bridge_to = [&](size_t i, const ConstraintID & witness, size_t witness_position) -> optional<ProofLine> {
                    const auto & home = task_data[i].appearances.front();
                    if (home.donor == witness)
                        return std::nullopt; // already there, nothing to carry

                    auto key = pair{i, witness};
                    auto already = bridges.find(key);
                    if (already != bridges.end())
                        return already->second;

                    auto from = flags_for(tracker, home.donor, home.position, t);
                    auto to = flags_for(tracker, witness, witness_position, t);
                    if (! from || ! to)
                        throw ProofError{"inferred disjunctive: a resource that witnesses a conflict at time " + to_string(t.raw_value) +
                            " has no flags for one of the tasks it is about"};

                    auto line = recover_conjunction_flag_bridge(recipe_logger, std::get<2>(*from), {std::get<0>(*from), std::get<1>(*from)},
                        std::get<2>(*to), {std::get<0>(*to), std::get<1>(*to)}, ProofLevel::Temporary);
                    if (stats)
                        ++stats->bridges_derived;
                    bridges.emplace(key, line);
                    return line;
                };

                // The pairwise at-most-ones, each out of its witness's capacity
                // row: weaken every other task out, saturate, divide by the
                // margin. Then carry it onto the flags this constraint is
                // expressed in.
                vector<vector<ProofLine>> at_most_ones(here.size());
                for (size_t b = 1; b < here.size(); ++b)
                    for (size_t a = 0; a < b; ++a) {
                        const auto & c = *conflicts[here[a]][here[b]];
                        auto row = rows.find(c.witness);
                        if (row == rows.end())
                            return std::nullopt;

                        // Reduced to the constant-argument form the at-most-one
                        // program reads it as: the witness's set-aside tasks
                        // weakened away, and a variable capacity replaced by the
                        // number `c.capacity` already holds.
                        const auto & witness_view = views.at(c.witness);
                        auto reduced = recover_constant_argument_row(recipe_logger, witness_view, c.witness, row->second, t, ProofLevel::Temporary);
                        if (! reduced)
                            return std::nullopt;

                        auto u_flags = flags_for(tracker, c.witness, c.witness_position_u, t);
                        auto v_flags = flags_for(tracker, c.witness, c.witness_position_v, t);
                        if (! u_flags || ! v_flags)
                            return std::nullopt;

                        // Everything else on that resource that could be running
                        // now has to come out of the row first. Over the
                        // witness's *usable* positions: a task that demands
                        // nothing of this resource has no term in the row and no
                        // flags either, and one that was set aside had its terms
                        // taken out by the reduction above --- weakening either
                        // again would be `w` on a variable the constraint does
                        // not mention, which VeriPB refuses.
                        vector<ProofFlag> weaken_out;
                        for (auto other : witness_view.usable) {
                            if (other == c.witness_position_u || other == c.witness_position_v)
                                continue;
                            auto other_flags = flags_for(tracker, c.witness, other, t);
                            if (other_flags)
                                weaken_out.push_back(std::get<2>(*other_flags));
                        }

                        // Not emitted: the at-most-one is only ever the opening
                        // of this `pol`, which goes on to carry it onto this
                        // constraint's own flags below. Two members, which is
                        // the pairwise case of the same program --- and where
                        // a clique's members share a witness, recovering their
                        // sub-clique in one step instead is what issue #666
                        // is about.
                        PolBuilder pair_amo;
                        [[maybe_unused]] auto at_most =
                            build_am1_from_row(pair_amo, *reduced, {c.demand_u, c.demand_v}, weaken_out, c.capacity, tracker);

                        // Bridging a task onto the *other* task's flags leaves
                        // its own term uncancelled, so what is merged is not the
                        // at-most-one for this pair at all.
                        // Carrying the at-most-one onto this constraint's own
                        // flags continues the same `pol` rather than starting
                        // another: the bridges just go on the stack, each
                        // cancelling its task's term and leaving the other, and
                        // one saturation clears up after all of it. A line per
                        // pair per time point saved, which over a horizon is the
                        // difference worth having.
                        auto bridged_u = bridge_to(here[a], c.witness, bridge_wrong_task ? c.witness_position_v : c.witness_position_u);
                        auto bridged_v = bridge_to(here[b], c.witness, c.witness_position_v);
                        if (bridged_u)
                            pair_amo.add(*bridged_u);
                        if (bridged_v)
                            pair_amo.add(*bridged_v);
                        if (bridged_u || bridged_v)
                            pair_amo.saturate();
                        at_most_ones[b].push_back(pair_amo.emit(recipe_logger, ProofLevel::Temporary));
                    }

                return recover_am1_from_pairs(recipe_logger, flags, at_most_ones, ProofLevel::Top,
                    claim_rhs_zero ? Am1FromPairsMutation{am1_from_pairs_mutation::ClaimOneMore{}}
                                   : Am1FromPairsMutation{am1_from_pairs_mutation::None{}});
            },
            .makespan = _makespan,
            .makespan_links = links,
            .makespan_bound_reached =
                [stats = _stats](Integer bound) {
                    if (stats && bound > stats->certified_makespan_bound)
                        stats->certified_makespan_bound = bound;
                },
            .makespan_mutation = std::holds_alternative<inferred_disjunctive_mutation::ClaimHigherMakespanBound>(_mutation)
                ? makespan_energy::MakespanEnergyMutation{makespan_energy::makespan_energy_mutation::ClaimHigherBound{}}
                : makespan_energy::MakespanEnergyMutation{makespan_energy::makespan_energy_mutation::None{}},
            .rules = _rules};

        if (! install_derived_cumulative(propagators, state, logger, move(spec))) {
            bump(&InferredDisjunctiveStats::declined_by_install);
            continue;
        }

        bump(&InferredDisjunctiveStats::cliques_posted);
        bump(&InferredDisjunctiveStats::clique_members_posted, clique.size());
        auto bound = capacity_bound(clique);
        if (_stats && bound > _stats->largest_capacity_bound)
            _stats->largest_capacity_bound = bound;
        if (logger)
            logger->emit_proof_comment(
                "presolve disjunctive: inferred a clique of " + to_string(clique.size()) + " tasks, total duration " + to_string(bound.raw_value));
    }

    // How much of this genuinely spanned resources, which is what says a
    // fixture is exercising the cross-resource case rather than something a
    // single Cumulative could have found.
    for (const auto & [u, v] : candidate_pairs) {
        const auto & c = *conflict[u][v];
        if (tasks[u].appearances.front().donor != c.witness || tasks[v].appearances.front().donor != c.witness)
            bump(&InferredDisjunctiveStats::cross_donor_pairs);
    }

    return true;
}

auto InferredDisjunctive::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<InferredDisjunctive>(_stats);
    result->with_budgets(_max_candidates, _max_posted);
    result->with_minimum_clique_size(_min_clique_size);
    result->with_rules(_rules);
    result->with_proof_mutation(_mutation);
    if (_makespan)
        result->with_makespan(*_makespan);
    return result;
}
