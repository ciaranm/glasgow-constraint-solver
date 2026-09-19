#include <gcs/constraints/equals/equals.hh>
#include <gcs/constraints/parity/gf2_system.hh>
#include <gcs/constraints/parity/parity.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/presolvers/parity_system_gathering/parity_system_gathering.hh>
#include <gcs/problem.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <concepts>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace gcs;
using namespace gcs::innards;

using std::make_optional;
using std::make_shared;
using std::make_unique;
using std::move;
using std::nullopt;
using std::shared_ptr;
using std::size_t;
using std::string;
using std::to_string;
using std::unique_ptr;
using std::vector;

ParitySystemGathering::ParitySystemGathering(shared_ptr<ParitySystemGatheringStats> stats) :
    // Always a block, whether or not anyone asked for one, as
    // CumulativeStrengthening and DifferenceLogic both do it: what reaches a
    // report is what was registered, and a presolver that registers nothing is a
    // presolver that cannot be told apart from one that did nothing.
    _stats(stats ? move(stats) : make_shared<ParitySystemGatheringStats>()), _keep_donor_propagators(false)
{
}

auto ParitySystemGathering::keeping_donor_propagators(bool keep) -> ParitySystemGathering &
{
    _keep_donor_propagators = keep;
    return *this;
}

auto ParitySystemGathering::clone() const -> unique_ptr<Presolver>
{
    auto result = make_unique<ParitySystemGathering>(_stats);
    result->keeping_donor_propagators(_keep_donor_propagators);
    return result;
}

namespace
{
    // A donor that survived every check, with what the propagator will need.
    struct Candidate
    {
        ParitySystemRow row;
        ConstraintID donor;
    };

    // Union-find over atom indices, for splitting the gathered rows into the
    // components that can actually inform each other.
    class Components
    {
    private:
        vector<size_t> _parent;

    public:
        explicit Components(size_t n) : _parent(n)
        {
            std::iota(_parent.begin(), _parent.end(), size_t{0});
        }

        auto find(size_t x) -> size_t
        {
            while (_parent[x] != x) {
                _parent[x] = _parent[_parent[x]];
                x = _parent[x];
            }
            return x;
        }

        auto merge(size_t a, size_t b) -> void
        {
            _parent[find(a)] = find(b);
        }
    };
}

auto ParitySystemGathering::run(Problem & problem, Propagators & propagators, State & initial_state, ProofLogger * const logger) -> bool
{
    // Registered before anything is decided, so that a run which gathers nothing
    // still reports having looked. The counters are filled in at the end, into
    // this same object.
    propagators.add_component_stats(_stats);

    ParitySystemGatheringStats stats;

    // ParityOdd is what Problem stores --- its clone() returns its own type, and
    // it has no hierarchy to flatten within --- so that is what to ask for. The
    // residual that this cannot pin is that clone() might one day return
    // something else entirely, at which point the enumeration would silently find
    // nothing; gcs/constraint_enumeration_test.cc is what holds that down, and
    // the counts below are what would notice.
    vector<Candidate> candidates;
    for (const auto & c : problem.each_constraint_of_type<ParityOdd>()) {
        if (c.literals().empty()) {
            ++stats.skipped_empty_row;
            continue;
        }

        // With no logger there is nothing to cite and nothing to check, so a
        // chain is neither looked for nor needed.
        std::optional<ParitySlackSource> slack_source;
        if (logger) {
            auto chain = find_parity_chain(*logger, c.constraint_id(), ConstraintProofModelData<ParityOdd>::chain_naming(), c.literals().size());
            if (! chain) {
                ++stats.skipped_uncitable_chain;
                continue;
            }
            slack_source = ParitySlackSource{*chain};
        }

        candidates.push_back(
            Candidate{ParitySystemRow{c.literals(), move(slack_source), "pgather" + as_string(c.constraint_id()) + "_"}, c.constraint_id()});
    }

    // Boolean Equals / NotEquals are 2-XORs when both operands are within
    // {0, 1}: `x = y` is `[x != 0] XOR [y != 0] = 0`, which as an odd row is the
    // same with one literal negated, and `x != y` is the odd row directly. This
    // is where a MiniZinc model's bool_eq and bool_not rows come from, and they
    // are worth having because they are the edges that join what would otherwise
    // be separate XOR components.
    //
    // Both are ReifiedEquals, which is what clone() returns, so that is what to
    // ask for; the reification condition is what says which. Neither needs a row
    // cited: with two literals B is zero, and both halves of the slack form are
    // plain RUP against the rows the donor itself emitted.
    static_assert(std::derived_from<Equals, ReifiedEquals>);
    static_assert(std::derived_from<NotEquals, ReifiedEquals>);

    for (const auto & c : problem.each_constraint_of_type<ReifiedEquals>()) {
        auto unconditional = false;
        overloaded{//
            [&](const reif::MustHold &) { unconditional = true; }, [&](const reif::MustNotHold &) { unconditional = true; }, [&](const auto &) {}}
            .visit(c.reification_condition());
        if (! unconditional) {
            // A conditional equality is not a parity row at all until the
            // condition is decided, and the system has no vocabulary for that.
            ++stats.skipped_reified;
            continue;
        }

        auto within_a_bit = [&](const IntegerVariableID & v) {
            auto [lower, upper] = initial_state.bounds(v);
            return lower >= 0_i && upper <= 1_i;
        };
        if (! within_a_bit(c.left_variable()) || ! within_a_bit(c.right_variable())) {
            // Over wider operands equality is not a parity constraint: `x = y`
            // says far more than "the same number of them are non-zero".
            ++stats.skipped_wide_operands;
            continue;
        }

        // Odd parity either way: for an equality one literal is negated, which
        // is exactly `!p = p XOR 1`.
        Literals literals{c.left_variable() != 0_i, c.enforces_equality() ? c.right_variable() == 0_i : c.right_variable() != 0_i};
        candidates.push_back(Candidate{ParitySystemRow{move(literals), logger ? make_optional(ParitySlackSource{ParitySlackFormIsRUP{}}) : nullopt,
                                           "pgather" + as_string(c.constraint_id()) + "_"},
            c.constraint_id()});
        ++stats.boolean_rows_offered;
    }

    // Canonicalise once, over every candidate together, so that two donors
    // mentioning the same fact land in the same column and so in the same
    // component. A row whose atoms all cancelled --- `ParityOdd({x, x})` --- has
    // none, shares none, and so is alone by construction.
    vector<Literals> all_literals;
    for (const auto & candidate : candidates)
        all_literals.push_back(candidate.row.literals);
    auto system = build_gf2_system(all_literals);

    Components components{system.atoms.size()};
    for (const auto & row : system.rows) {
        auto atoms = row.atoms.set_indices();
        for (size_t i = 1; i < atoms.size(); ++i)
            components.merge(atoms[0], atoms[i]);
    }

    // Group the candidates by the component of their first atom. An atom-less
    // row gets a group of its own, which is then skipped by the size gate below.
    std::map<std::optional<size_t>, vector<size_t>> grouped;
    for (const auto & [r, row] : enumerate(system.rows)) {
        auto first = row.atoms.first_set();
        grouped[first ? make_optional(components.find(*first)) : nullopt].push_back(r);
    }

    vector<ConstraintID> gathered_donors;
    for (const auto & [component, members] : grouped) {
        // Fewer than two rows is not a threshold, it is a degeneracy: over a
        // single row the system propagator computes exactly what that row's own
        // ParityOdd computes, so installing one buys nothing and costs a wake.
        // The atom-less rows all land in one nullopt group, which is why this
        // counts members rather than trusting the group to be a real component.
        if (! component || members.size() < 2) {
            stats.skipped_alone_in_component += members.size();
            continue;
        }

        vector<ParitySystemRow> rows;
        for (const auto & r : members) {
            rows.push_back(candidates[r].row);
            gathered_donors.push_back(candidates[r].donor);
        }

        // A presolver-derived propagator has no posted-constraint identity of
        // its own, exactly as for AutoTable and DifferenceLogic. No row it
        // installs can be empty --- those were skipped above --- so the
        // contradiction path inside is unreachable from here.
        install_parity_system_propagator(propagators, CurrentlyUnnamedConstraint{}, "parity_system", move(rows));
        ++stats.components_installed;
        stats.rows_gathered += members.size();

        // Atoms of the components that got a propagator, not of every candidate:
        // a reader comparing this against rows_gathered is asking how big the
        // systems being eliminated over are, and rows that were skipped are not
        // in one.
        for (size_t a = 0; a != system.atoms.size(); ++a)
            if (components.find(a) == *component)
                ++stats.atoms;
    }

    if (0 != stats.components_installed && ! _keep_donor_propagators)
        stats.donor_propagators_disabled = propagators.disable_propagators_for_constraints(gathered_donors);

    // Assigning rather than replacing is what keeps a caller's handle, and the
    // block registered at the top of this function, the same object.
    *_stats = stats;

    return true;
}

auto ParitySystemGatheringStats::component_name() const -> string
{
    return "parity_system_gathering";
}

auto ParitySystemGatheringStats::summary() const -> string
{
    if (0 == rows_gathered)
        return "gathered nothing";

    auto result = to_string(rows_gathered) + " rows gathered over " + to_string(atoms) + " atoms into " + to_string(components_installed) +
        (1 == components_installed ? " system" : " systems");

    // "offered" and not "of them": such a row still has to land in a component
    // with something else to be gathered at all. Worth saying even when it is
    // zero, because a model whose XORs all arrived as ParityOdd looks identical
    // to one where the Boolean detection has stopped working, and this is the
    // line that separates them.
    result += ", with " + to_string(boolean_rows_offered) + " rows offered by a Boolean equality";

    if (0 != donor_propagators_disabled)
        result += ", retiring " + to_string(donor_propagators_disabled) + " donor propagators";

    return result;
}

auto ParitySystemGatheringStats::entries() const -> vector<StatsEntry>
{
    return {StatsEntry{"rows_gathered", static_cast<long long>(rows_gathered)}, StatsEntry{"atoms", static_cast<long long>(atoms)},
        StatsEntry{"components_installed", static_cast<long long>(components_installed)},
        StatsEntry{"donor_propagators_disabled", static_cast<long long>(donor_propagators_disabled)},
        StatsEntry{"skipped_empty_row", static_cast<long long>(skipped_empty_row)},
        StatsEntry{"skipped_uncitable_chain", static_cast<long long>(skipped_uncitable_chain)},
        StatsEntry{"skipped_alone_in_component", static_cast<long long>(skipped_alone_in_component)},
        StatsEntry{"boolean_rows_offered", static_cast<long long>(boolean_rows_offered)},
        StatsEntry{"skipped_reified", static_cast<long long>(skipped_reified)},
        StatsEntry{"skipped_wide_operands", static_cast<long long>(skipped_wide_operands)}};
}
