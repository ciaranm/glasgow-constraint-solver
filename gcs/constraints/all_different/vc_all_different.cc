#include <gcs/constraints/all_different/vc_all_different.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>
#include <util/enumerate.hh>

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <optional>
#include <sstream>
#include <type_traits>
#include <utility>
#include <variant>

using namespace gcs;
using namespace gcs::innards;

using std::adjacent_find;
using std::cmp_not_equal;
using std::count;
using std::decay_t;
using std::function;
using std::is_same_v;
using std::list;
using std::map;
using std::min;
using std::nullopt;
using std::optional;
using std::pair;
using std::sort;
using std::stringstream;
using std::unique_ptr;
using std::variant;
using std::vector;
using std::visit;

auto gcs::innards::propagate_non_gac_alldifferent(const ConstraintStateHandle & unassigned_handle, State & state) -> innards::Inference
{
    auto & unassigned = any_cast<list<IntegerVariableID> &>(state.get_constraint_state(unassigned_handle));

    auto result = Inference::NoChange;
    vector<pair<IntegerVariableID, Integer>> to_propagate;
    {
        // Collect any newly assigned values
        for (auto i = unassigned.begin(); i != unassigned.end();) {
            auto s = *i;
            if (auto val = state.optional_single_value(s)) {
                to_propagate.emplace_back(s, *val);
                unassigned.erase(i++);
            }
            else
                i++;
        }
    }

    while (! to_propagate.empty()) {
        auto [var, val] = to_propagate.back();
        to_propagate.pop_back();
        auto i = unassigned.begin();

        for (auto other : to_propagate) {
            if (other.second == val) return Inference::Contradiction;
        }

        while (i != unassigned.end()) {
            auto other = *i;
            if (other != var) {
                increase_inference_to(result, state.infer_not_equal(other, val, JustifyUsingRUP{}));
                if (result == Inference::Contradiction) return Inference::Contradiction;
                if (auto other_val = state.optional_single_value(other)) {
                    to_propagate.emplace_back(other, *other_val);
                    unassigned.erase(i++);
                }
                else
                    ++i;
            }
        }
    }
    return result;
}

auto gcs::innards::define_clique_not_equals_encoding(gcs::innards::State & state, gcs::innards::Propagators & propagators, const vector<gcs::IntegerVariableID> & vars) -> void
{
    for (unsigned i = 0; i < vars.size(); ++i)
        for (unsigned j = i + 1; j < vars.size(); ++j) {
            auto selector = propagators.create_proof_flag("notequals");
            propagators.define(state, WeightedPseudoBooleanSum{} + 1_i * vars[i] + -1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{selector});
            propagators.define(state, WeightedPseudoBooleanSum{} + -1_i * vars[i] + 1_i * vars[j] <= -1_i, HalfReifyOnConjunctionOf{! selector});
        }
}

VCAllDifferent::VCAllDifferent(vector<IntegerVariableID> v) :
    _vars(move(v))
{
}

auto VCAllDifferent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<VCAllDifferent>(_vars);
}

auto VCAllDifferent::install(Propagators & propagators, State & initial_state) && -> void
{
    if (propagators.want_definitions()) {
        define_clique_not_equals_encoding(initial_state, propagators, _vars);
    }

    auto sanitised_vars = move(_vars);
    sort(sanitised_vars.begin(), sanitised_vars.end());
    if (sanitised_vars.end() != adjacent_find(sanitised_vars.begin(), sanitised_vars.end()))
        throw UnexpectedException{"not sure what to do about duplicate variables in an alldifferent"};

    Triggers triggers;
    triggers.on_change = {sanitised_vars.begin(), sanitised_vars.end()};
    vector<Integer> compressed_vals;

    // Keep track of unassigned vars
    // Might want a more centralised way of doing this in future.
    list<IntegerVariableID> unassigned{};
    for (auto & var : sanitised_vars)
        if (! initial_state.has_single_value(var))
            unassigned.push_back(var);

    auto unassigned_handle = initial_state.add_constraint_state(unassigned);

    propagators.install(
        [vars = move(sanitised_vars), unassigned_handle = unassigned_handle,
            vals = move(compressed_vals)](State & state) -> pair<Inference, PropagatorState> {
            return pair{propagate_non_gac_alldifferent(unassigned_handle, state), PropagatorState::Enable};
        },
        triggers, "vcalldiff");
}

auto VCAllDifferent::describe_for_proof() -> std::string
{
    return "all different";
}
