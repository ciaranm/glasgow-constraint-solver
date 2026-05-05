#include <gcs/constraints/all_different/encoding.hh>
#include <gcs/constraints/all_different/gac_all_different.hh>
#include <gcs/constraints/all_different/symmetric_all_different.hh>
#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>

#include <util/enumerate.hh>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <map>
#include <sstream>
#include <utility>

using namespace gcs;
using namespace gcs::innards;

using std::make_shared;
using std::make_unique;
using std::map;
using std::move;
using std::shared_ptr;
using std::string;
using std::stringstream;
using std::unique_ptr;
using std::vector;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::print;
#else
using fmt::print;
#endif

SymmetricAllDifferent::SymmetricAllDifferent(vector<IntegerVariableID> vars, Integer start) :
    _vars(move(vars)),
    _start(start)
{
}

auto SymmetricAllDifferent::clone() const -> unique_ptr<Constraint>
{
    return make_unique<SymmetricAllDifferent>(_vars, _start);
}

auto SymmetricAllDifferent::install(Propagators & propagators, State & initial_state, ProofModel * const optional_model) && -> void
{
    auto vars = move(_vars);
    auto start = _start;
    auto n = vars.size();

    for (const auto & v : vars) {
        propagators.trim_lower_bound(initial_state, optional_model, v, start, "SymmetricAllDifferent");
        propagators.trim_upper_bound(initial_state, optional_model, v, start + Integer(n) - 1_i, "SymmetricAllDifferent");
    }

    shared_ptr<map<Integer, ProofLine>> value_am1s;

    if (optional_model) {
        // x_i = j  iff  x_j = i, posted as two implications per (i, j) with
        // i < j. (The pair (j, i) gives the same two implications swapped, so
        // iterating only i < j is enough — half of what Inverse(x, y) emits
        // for general x and y.)
        for (size_t i = 0; i < n; ++i)
            for (size_t j = i + 1; j < n; ++j) {
                optional_model->add_constraint("SymmetricAllDifferent", "x_i = j -> x_j = i",
                    WPBSum{} + 1_i * (vars[i] != Integer(j) + start)
                        + 1_i * (vars[j] == Integer(i) + start) >= 1_i);
                optional_model->add_constraint("SymmetricAllDifferent", "x_j = i -> x_i = j",
                    WPBSum{} + 1_i * (vars[j] != Integer(i) + start)
                        + 1_i * (vars[i] == Integer(j) + start) >= 1_i);
            }

        define_clique_not_equals_encoding(*optional_model, vars);

        // Per-value am1s for the alldiff hall-set / SCC justifications,
        // built once at the root.
        value_am1s = make_shared<map<Integer, ProofLine>>();
        if (n >= 2) {
            propagators.install_initialiser(
                [vars, start, n, value_am1s](
                    const State &, auto &, ProofLogger * const logger) -> void {
                    for (Integer v = start; v < start + Integer(n); ++v) {
                        vector<IntegerVariableCondition> xieqvs;
                        for (const auto & var : vars)
                            xieqvs.push_back(var != v);
                        value_am1s->emplace(v, recover_am1<IntegerVariableCondition>(
                                                   *logger, ProofLevel::Top, xieqvs,
                                                   [&](const IntegerVariableCondition & c1, const IntegerVariableCondition & c2) -> ProofLine {
                                                       return logger->emit(RUPProofRule{},
                                                           WPBSum{} + 1_i * c1 + 1_i * c2 >= 1_i, ProofLevel::Temporary);
                                                   }));
                    }
                });
        }
    }

    Triggers triggers;
    triggers.on_change.insert(triggers.on_change.end(), vars.begin(), vars.end());

    vector<Integer> values;
    for (size_t i = 0; i < n; ++i)
        values.push_back(start + Integer(i));

    propagators.install(
        [vars, start, values = move(values), value_am1s = move(value_am1s)](
            const State & state, auto & inf, ProofLogger * const logger) -> PropagatorState {
            // Channeling: x_i = v  =>  x_v = i. If i is not in D(x_v), prune
            // v from D(x_i). Single pass — Inverse(x, y) runs this in both
            // directions, but with x = y the two passes are identical.
            for (const auto & [i, x_i] : enumerate(vars)) {
                for (auto v : state.each_value_mutable(x_i))
                    if (! state.in_domain(vars.at((v - start).as_index()), Integer(i) + start))
                        inf.infer(logger, x_i != v,
                            JustifyUsingRUP{},
                            [&]() { return Reason{vars.at((v - start).as_index()) != Integer(i) + start}; });
            }

            propagate_gac_all_different(vars, values, vector<Integer>{}, *value_am1s.get(), state, inf, logger);
            return PropagatorState::Enable;
        },
        triggers, "symmetric_all_different");
}

auto SymmetricAllDifferent::s_exprify(const string & name, const ProofModel * const model) const -> string
{
    stringstream s;

    print(s, "{} symmetric_all_different (", name);
    for (const auto & var : _vars)
        print(s, " {}", model->names_and_ids_tracker().s_expr_name_of(var));
    print(s, ") {}", _start);

    return s.str();
}
