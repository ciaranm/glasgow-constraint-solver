#include <gcs/exception.hh>

#include <gcs/innards/extensional_utils.hh>
#include <gcs/innards/linear_utils.hh>
#include <gcs/innards/proof.hh>
#include <gcs/innards/propagators.hh>

#include <util/enumerate.hh>
#include <util/overloaded.hh>

#include <algorithm>
#include <bit>
#include <chrono>
#include <list>

using namespace gcs;
using namespace gcs::innards;

using std::atomic;
using std::bit_ceil;
using std::list;
using std::make_optional;
using std::move;
using std::nullopt;
using std::optional;
using std::pair;
using std::string;
using std::vector;
using std::visit;

namespace
{
    struct TriggerIDs
    {
        vector<int> on_change;
        vector<int> on_bounds;
        vector<int> on_instantiated;
    };
}

struct Propagators::Imp
{
    optional<Proof> & optional_proof;

    vector<PropagationFunction> propagation_functions;
    vector<InitialisationFunction> initialisation_functions;

    vector<uint8_t> propagator_is_disabled;
    unsigned long long total_propagations = 0, effectful_propagations = 0, contradicting_propagations = 0;
    vector<TriggerIDs> iv_triggers;
    vector<long> degrees;
    bool first = true;

    Imp(optional<Proof> & o) :
        optional_proof(o)
    {
    }
};

Propagators::Propagators(optional<Proof> & o) :
    _imp(new Imp(o))
{
}

Propagators::~Propagators() = default;

Propagators::Propagators(Propagators &&) = default;

auto Propagators::operator=(Propagators &&) -> Propagators & = default;

auto Propagators::model_contradiction(const string & explain_yourself) -> void
{
    if (_imp->optional_proof)
        _imp->optional_proof->cnf({});

    install([explain_yourself = explain_yourself](State &) -> pair<Inference, PropagatorState> {
        return pair{Inference::Contradiction, PropagatorState::Enable};
    },
        Triggers{}, "model contradiction");
}

auto Propagators::trim_lower_bound(const State & state, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.lower_bound(var) < val) {
        if (state.upper_bound(var) >= val) {
            define_cnf(state, {var >= val});
            install([var, val](State & state) {
                return pair{state.infer(var >= val, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, "trimmed lower bound");
        }
        else
            model_contradiction("Trimmed lower bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::trim_upper_bound(const State & state, IntegerVariableID var, Integer val, const string & x) -> void
{
    if (state.upper_bound(var) > val) {
        if (state.lower_bound(var) <= val) {
            define_cnf(state, {var < val + 1_i});
            install([var, val](State & state) {
                return pair{state.infer(var < val + 1_i, JustifyUsingRUP{}), PropagatorState::DisableUntilBacktrack};
            },
                Triggers{}, "trimmed upper bound");
        }
        else
            model_contradiction("Trimmed upper bound of " + debug_string(var) + " due to " + x + " is outside its domain");
    }
}

auto Propagators::define_cnf(const State &, Literals && c) -> optional<ProofLine>
{
    optional<ProofLine> result = nullopt;

    if (_imp->optional_proof)
        if (sanitise_literals(c))
            result = _imp->optional_proof->cnf(c);

    return result;
}

auto Propagators::define_at_most_one(const State &, Literals && lits) -> optional<ProofLine>
{
    if (_imp->optional_proof)
        return _imp->optional_proof->at_most_one(move(lits));
    else
        return nullopt;
}

auto Propagators::define_pseudoboolean_ge(const State &, WeightedPseudoBooleanSum && lits, Integer val,
    optional<ReificationTerm> half_reif) -> optional<ProofLine>
{
    if (_imp->optional_proof) {
        if (sanitise_pseudoboolean_terms(lits, val))
            return _imp->optional_proof->pseudoboolean_ge(lits, val, half_reif, false);
    }
    return nullopt;
}

auto Propagators::define_pseudoboolean_eq(const State &, WeightedPseudoBooleanSum && lits, Integer val,
    optional<ReificationTerm> half_reif) -> optional<ProofLine>
{
    if (_imp->optional_proof) {
        if (sanitise_pseudoboolean_terms(lits, val))
            return _imp->optional_proof->pseudoboolean_ge(lits, val, half_reif, true);
    }
    return nullopt;
}

auto Propagators::define_linear_le(const State & state, const WeightedSum & coeff_vars,
    Integer value, optional<ReificationTerm> half_reif) -> optional<ProofLine>
{
    if (_imp->optional_proof) {
        auto [cv, modifier] = simplify_linear(coeff_vars);
        return _imp->optional_proof->integer_linear_le(state, cv, value + modifier, half_reif, false);
    }
    else
        return nullopt;
}

auto Propagators::define_linear_eq(const State & state, const WeightedSum & coeff_vars,
    Integer value, optional<ReificationTerm> half_reif) -> optional<ProofLine>
{
    if (_imp->optional_proof) {
        auto [cv, modifier] = simplify_linear(coeff_vars);
        return _imp->optional_proof->integer_linear_le(state, cv, value + modifier, half_reif, true);
    }
    else
        return nullopt;
}

auto Propagators::install(PropagationFunction && f, const Triggers & triggers, const std::string &) -> void
{
    int id = _imp->propagation_functions.size();
    _imp->propagation_functions.emplace_back(move(f));
    _imp->propagator_is_disabled.push_back(0);

    for (const auto & v : triggers.on_change) {
        trigger_on_change(v, id);
        increase_degree(v);
    }

    for (const auto & v : triggers.on_bounds) {
        trigger_on_bounds(v, id);
        increase_degree(v);
    }

    for (const auto & v : triggers.on_instantiated) {
        trigger_on_instantiated(v, id);
        increase_degree(v);
    }
}

auto Propagators::install_initialiser(InitialisationFunction && f) -> void
{
    _imp->initialisation_functions.emplace_back(move(f));
}

namespace
{
    auto is_immediately_infeasible(const IntegerVariableID & var, const Integer & val) -> bool
    {
        return is_literally_false(var == val);
    }

    auto is_immediately_infeasible(const IntegerVariableID &, const Wildcard &) -> bool
    {
        return false;
    }

    auto is_immediately_infeasible(const IntegerVariableID & var, const IntegerOrWildcard & val) -> bool
    {
        return visit([&](const auto & val) { return is_immediately_infeasible(var, val); }, val);
    }

    auto add_lit_unless_immediately_true(WeightedPseudoBooleanSum & lits, const IntegerVariableID & var, const Integer & val) -> void
    {
        if (! is_literally_true(var == val))
            lits += 1_i * (var == val);
    }

    auto add_lit_unless_immediately_true(WeightedPseudoBooleanSum &, const IntegerVariableID &, const Wildcard &) -> void
    {
    }

    auto add_lit_unless_immediately_true(WeightedPseudoBooleanSum & lits, const IntegerVariableID & var, const IntegerOrWildcard & val) -> void
    {
        return visit([&](const auto & val) { add_lit_unless_immediately_true(lits, var, val); }, val);
    }

    template <typename T_>
    auto depointinate(const std::shared_ptr<const T_> & t) -> const T_ &
    {
        return *t;
    }

    template <typename T_>
    auto depointinate(const T_ & t) -> const T_ &
    {
        return t;
    }
}

auto Propagators::define_and_install_table(State & state, const vector<IntegerVariableID> & vars,
    ExtensionalTuples permitted, const string & x) -> void
{
    visit([&](auto && permitted) {
        if (depointinate(permitted).empty()) {
            model_contradiction("Empty table constraint from " + x);
            return;
        }

        int id = _imp->propagation_functions.size();
        auto selector = create_auxilliary_integer_variable(state, 0_i, Integer(depointinate(permitted).size() - 1), "table",
            IntegerVariableProofRepresentation::DirectOnly);

        // pb encoding, if necessary
        if (want_definitions()) {
            for (const auto & [tuple_idx, tuple] : enumerate(depointinate(permitted))) {
                // selector == tuple_idx -> /\_i vars[i] == tuple[i]
                bool infeasible = false;
                WeightedPseudoBooleanSum lits;
                lits += Integer(tuple.size()) * (selector != Integer(tuple_idx));
                for (const auto & [var_idx, var] : enumerate(vars)) {
                    if (is_immediately_infeasible(var, tuple[var_idx]))
                        infeasible = true;
                    else
                        add_lit_unless_immediately_true(lits, var, tuple[var_idx]);
                }
                if (infeasible)
                    define_cnf(state, {selector != Integer(tuple_idx)});
                else
                    define_pseudoboolean_ge(state, move(lits), Integer(lits.terms.size() - 1));
            }
        }

        // set up triggers before we move vars away
        for (auto & v : vars)
            trigger_on_change(v, id);
        trigger_on_change(selector, id);

        _imp->propagation_functions.emplace_back([&, table = ExtensionalData{selector, move(vars), move(permitted)}](
                                                     State & state) -> pair<Inference, PropagatorState> {
            return propagate_extensional(table, state);
        });
        _imp->propagator_is_disabled.push_back(0);
    },
        move(permitted));
}

auto Propagators::initialise(State & state) const -> void
{
    for (auto & f : _imp->initialisation_functions)
        f(state);
}

auto Propagators::requeue_all_propagators() -> void
{
    _imp->first = true;
    fill(_imp->propagator_is_disabled.begin(), _imp->propagator_is_disabled.end(), 0);
}

auto Propagators::propagate(State & state, atomic<bool> * optional_abort_flag) const -> bool
{
    vector<int> on_queue(_imp->propagation_functions.size(), 0);
    unsigned propagation_queue_first = 0, propagation_queue_end = 0;
    unsigned propagation_queue_size = bit_ceil(_imp->propagation_functions.size() + 1);
    unsigned propagation_queue_mask = propagation_queue_size - 1;
    vector<int> propagation_queue;
    propagation_queue.reserve(propagation_queue_size);
    vector<int> newly_disabled_propagators;

    switch (state.infer_on_objective_variable_before_propagation()) {
    case Inference::NoChange: break;
    case Inference::Change: break;
    case Inference::Contradiction: return false;
    }

    if (_imp->first) {
        _imp->first = false;
        for (unsigned i = 0; i != _imp->propagation_functions.size(); ++i) {
            propagation_queue[propagation_queue_end++] = i;
            propagation_queue_end = propagation_queue_end & propagation_queue_mask;
            on_queue[i] = 1;
        }
    }

    bool contradiction = false;
    while (! contradiction) {
        if (propagation_queue_first == propagation_queue_end) {
            state.extract_changed_variables([&](SimpleIntegerVariableID v, HowChanged h) {
                if (v.index < _imp->iv_triggers.size()) {
                    auto & triggers = _imp->iv_triggers[v.index];

                    // the 0 == (on_queue + is_disabled) thing is to turn two branches into
                    // one, and is really saying (! on_queue && ! is_disabled). annoyingly,
                    // this is a hotspot in some benchmarks...

                    if (h == HowChanged::Instantiated)
                        for (auto & p : triggers.on_instantiated)
                            if (0 == (on_queue[p] + _imp->propagator_is_disabled[p])) {
                                propagation_queue[propagation_queue_end++] = p;
                                propagation_queue_end = propagation_queue_end & propagation_queue_mask;
                                on_queue[p] = 1;
                            }

                    if (h != HowChanged::InteriorValuesChanged)
                        for (auto & p : triggers.on_bounds)
                            if (0 == (on_queue[p] + _imp->propagator_is_disabled[p])) {
                                propagation_queue[propagation_queue_end++] = p;
                                propagation_queue_end = propagation_queue_end & propagation_queue_mask;
                                on_queue[p] = 1;
                            }

                    for (auto & p : triggers.on_change)
                        if (0 == (on_queue[p] + _imp->propagator_is_disabled[p])) {
                            propagation_queue[propagation_queue_end++] = p;
                            propagation_queue_end = propagation_queue_end & propagation_queue_mask;
                            on_queue[p] = 1;
                        }
                }
            });
        }

        if (propagation_queue_first == propagation_queue_end)
            break;

        int propagator_id = propagation_queue[propagation_queue_first++];
        propagation_queue_first = propagation_queue_first & propagation_queue_mask;
        on_queue[propagator_id] = 0;
        auto [inference, propagator_state] = _imp->propagation_functions[propagator_id](state);
        ++_imp->total_propagations;
        switch (inference) {
        case Inference::NoChange:
            break;
        case Inference::Change:
            ++_imp->effectful_propagations;
            break;
        case Inference::Contradiction:
            ++_imp->contradicting_propagations;
            contradiction = true;
            break;
        }

        if (! contradiction) {
            switch (propagator_state) {
            case PropagatorState::Enable:
                break;
            case PropagatorState::DisableUntilBacktrack:
                if (0 == _imp->propagator_is_disabled[propagator_id]) {
                    _imp->propagator_is_disabled[propagator_id] = 1;
                    newly_disabled_propagators.push_back(propagator_id);
                }
                break;
            }
        }

        if (optional_abort_flag && optional_abort_flag->load())
            return false;
    }

    if (! newly_disabled_propagators.empty()) {
        state.on_backtrack([&, to_enable = move(newly_disabled_propagators)]() {
            for (const auto & p : to_enable)
                _imp->propagator_is_disabled[p] = 0;
        });
    }

    return ! contradiction;
}

auto Propagators::create_auxilliary_integer_variable(State & state, Integer l, Integer u, const std::string & s,
    const IntegerVariableProofRepresentation rep) -> IntegerVariableID
{
    auto result = state.allocate_integer_variable_with_state(l, u);
    if (_imp->optional_proof)
        _imp->optional_proof->set_up_integer_variable(result, l, u, "aux_" + s, rep);
    return result;
}

auto Propagators::create_proof_flag(const std::string & n) -> ProofFlag
{
    if (! _imp->optional_proof)
        throw UnexpectedException{"trying to create a proof flag but proof logging is not enabled"};
    return _imp->optional_proof->create_proof_flag(n);
}

auto Propagators::create_proof_only_integer_variable(Integer l, Integer u, const std::string & s,
    const IntegerVariableProofRepresentation rep) -> ProofOnlySimpleIntegerVariableID
{
    if (! _imp->optional_proof)
        throw UnexpectedException{"trying to create a proof variable but proof logging is not enabled"};
    return _imp->optional_proof->create_proof_integer_variable(l, u, s, rep);
}

auto Propagators::want_definitions() const -> bool
{
    return _imp->optional_proof != nullopt;
}

auto Propagators::fill_in_constraint_stats(Stats & stats) const -> void
{
    stats.n_propagators += _imp->propagation_functions.size();
    stats.propagations += _imp->total_propagations;
    stats.effectful_propagations += _imp->effectful_propagations;
    stats.contradicting_propagations += _imp->contradicting_propagations;
}

auto Propagators::trigger_on_change(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].on_change.push_back(t);
        },
        [&](const ViewOfIntegerVariableID & v) {
            trigger_on_change(v.actual_variable, t);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::trigger_on_bounds(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].on_bounds.push_back(t);
        },
        [&](const ViewOfIntegerVariableID & v) {
            trigger_on_bounds(v.actual_variable, t);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::trigger_on_instantiated(IntegerVariableID var, int t) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->iv_triggers.size() <= v.index)
                _imp->iv_triggers.resize(v.index + 1);
            _imp->iv_triggers[v.index].on_instantiated.push_back(t);
        },
        [&](const ViewOfIntegerVariableID & v) {
            trigger_on_instantiated(v.actual_variable, t);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::increase_degree(IntegerVariableID var) -> void
{
    overloaded{
        [&](const SimpleIntegerVariableID & v) {
            if (_imp->degrees.size() < v.index + 1)
                _imp->degrees.resize(v.index + 1);
            ++_imp->degrees[v.index];
        },
        [&](const ViewOfIntegerVariableID & v) {
            increase_degree(v.actual_variable);
        },
        [&](const ConstantIntegerVariableID &) {
        }}
        .visit(var);
}

auto Propagators::degree_of(IntegerVariableID var) const -> long
{
    return overloaded{
        [&](const SimpleIntegerVariableID & v) -> long {
            if (v.index >= _imp->degrees.size())
                return 0;
            else
                return _imp->degrees[v.index];
        },
        [&](const ViewOfIntegerVariableID & v) -> long {
            return degree_of(v.actual_variable);
        },
        [&](const ConstantIntegerVariableID &) -> long {
            return 0;
        }}
        .visit(var);
}
