#include <gcs/constraints/smart_table/hints.hh>
#include <gcs/constraints/smart_table/smart_table.hh>
#include <gcs/exception.hh>
#include <gcs/innards/inference_tracker.hh>
#include <gcs/innards/justification.hh>
#include <gcs/innards/proofs/names_and_ids_tracker.hh>
#include <gcs/innards/proofs/proof_logger.hh>
#include <gcs/innards/proofs/proof_model.hh>
#include <gcs/innards/propagators.hh>
#include <gcs/innards/s_expr.hh>

#include <algorithm>
#include <gcs/proof.hh>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <variant>
#include <vector>

#include <version>

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
#include <format>
#include <print>
#else
#include <fmt/ostream.h>
#endif

#include <gcs/exception.hh>
#include <util/overloaded.hh>

using std::count;
using std::make_tuple;
using std::make_unique;
using std::map;
using std::move;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::tuple;
using std::unique_ptr;
using std::unordered_map;
using std::vector;
using std::ranges::copy_if;
using std::ranges::set_difference;
using std::ranges::set_intersection;
using std::ranges::sort;

#if defined(__cpp_lib_print) && defined(__cpp_lib_format)
using std::format;
using std::print;
using std::println;
#else
using fmt::format;
using fmt::print;
using fmt::println;
#endif

using namespace gcs;
using namespace gcs::innards;

namespace
{
    // Strip view info down to the underlying variable handle. Mirrors
    // smart_table's runtime `deview` (defined further down in this
    // file) so the construction-time alias check uses the same key the
    // build_forests / build_tree pipeline does.
    auto deview_for_alias_check(const IntegerVariableID & v) -> IntegerVariableID
    {
        return overloaded{
            [](const SimpleIntegerVariableID & s) -> IntegerVariableID { return s; },                       //
            [](const ViewOfIntegerVariableID & view) -> IntegerVariableID { return view.actual_variable; }, //
            [](const ConstantIntegerVariableID & c) -> IntegerVariableID { return c; }                      //
        }
            .visit(v);
    }
}

SmartTable::SmartTable(vector<IntegerVariableID> v, SmartTuples t) : _vars(move(v)), _tuples(move(t))
{
    // Aliased BinaryEntry endpoints break build_forests: both ends
    // hash to the same `deview` key, so adjacent_edges holds the entry
    // under one key with two copies, build_tree sees the second
    // endpoint as already visited (the root), and the edge silently
    // drops out of the tree — leaving the OPB encoding and propagator
    // at odds (silent wrong answer without --prove; rejection with).
    // Reject at construction. The check matches smart_table's own
    // deview (strips view info to the underlying variable), so
    // BinaryEntry{X, X+1, ...} is rejected too — both sides hash to
    // the same underlying var.
    for (const auto & tuple : _tuples)
        for (const auto & entry : tuple)
            if (auto * be = std::get_if<BinaryEntry>(&entry))
                if (deview_for_alias_check(be->var_1) == deview_for_alias_check(be->var_2))
                    throw InvalidProblemDefinitionException{
                        "SmartTable: BinaryEntry with aliased endpoints (both sides share the same underlying variable handle)"};

    // The same goes for any BinaryEntry that closes a cycle among a tuple's
    // underlying variables, including a second entry on a pair already joined:
    // build_tree finds both ends already visited and drops it (issue #1014). The
    // propagator relies on each tuple's binary entries forming a forest, which is
    // what lets it reach GAC without iterating, so reject a cycle rather than
    // handle it. An exact repeat of an entry already in the tuple is the one
    // exception: dropping it loses nothing, and AtMostOneSmartTable produces
    // them when its array repeats a variable.
    for (const auto & tuple : _tuples) {
        map<IntegerVariableID, IntegerVariableID> parent;
        auto find = [&](IntegerVariableID v) {
            while (parent.contains(v) && parent.at(v) != v)
                v = parent.at(v);
            return v;
        };

        set<std::tuple<IntegerVariableID, IntegerVariableID, SmartEntryConstraint>> seen;
        for (const auto & entry : tuple)
            if (auto * be = std::get_if<BinaryEntry>(&entry)) {
                if (! seen.emplace(be->var_1, be->var_2, be->constraint_type).second)
                    continue;
                auto root_1 = find(deview_for_alias_check(be->var_1));
                auto root_2 = find(deview_for_alias_check(be->var_2));
                if (root_1 == root_2)
                    throw InvalidProblemDefinitionException{
                        "SmartTable: the binary entries of a tuple form a cycle (each tuple's binary entries must form a forest)"};
                parent.insert_or_assign(root_1, root_2);
            }
    }
}

namespace
{
    // Shorthands
    using VariableDomainMap = unordered_map<IntegerVariableID, vector<Integer>>;
    using BinaryEntryData = tuple<IntegerVariableID, IntegerVariableID, SmartEntryConstraint>;
    using TreeEdges = vector<vector<SmartEntry>>;
    using Forest = vector<TreeEdges>;

    auto deview(IntegerVariableID v) -> IntegerVariableID
    {
        return overloaded{
            [&](SimpleIntegerVariableID & s) -> IntegerVariableID { return s; },                 //
            [&](ViewOfIntegerVariableID & v) -> IntegerVariableID { return v.actual_variable; }, //
            [&](ConstantIntegerVariableID & c) -> IntegerVariableID { return c; }                //
        }
            .visit(v);
    }

    // A VariableDomainMap is keyed by the underlying variable and holds values
    // in the underlying variable's space, so that every view of one variable in
    // a tuple reads and narrows the same set. These convert through a view on
    // the way in and out; for anything that is not a view they are the identity.
    auto to_view_value(const IntegerVariableID & v, Integer actual_value) -> Integer
    {
        if (auto * view = std::get_if<ViewOfIntegerVariableID>(&v))
            return (view->negate_first ? -actual_value : actual_value) + view->then_add;
        return actual_value;
    }

    auto to_actual_value(const IntegerVariableID & v, Integer view_value) -> Integer
    {
        if (auto * view = std::get_if<ViewOfIntegerVariableID>(&v))
            return view->negate_first ? -(view_value - view->then_add) : view_value - view->then_add;
        return view_value;
    }

    auto get_for_actual_var(const VariableDomainMap & vdom, const IntegerVariableID & v) -> vector<Integer>
    {
        vector<Integer> result;
        for (const auto & value : vdom.at(deview(v)))
            result.emplace_back(to_view_value(v, value));
        return result;
    }

    auto set_for_actual_var(VariableDomainMap & vdom, const IntegerVariableID & v, const vector<Integer> & vec) -> void
    {
        vector<Integer> result;
        for (const auto & value : vec)
            result.emplace_back(to_actual_value(v, value));
        vdom.at(deview(v)) = move(result);
    }

    auto log_filtering_inference(
        ProofLogger * const logger, const ProofFlag * tuple_selector, const Literal & lit, const State & state, auto &, const Reason & reason)
    {
        logger->emit_rup_proof_line_under_reason(
            eager_reason(reason, state), WPBSum{} + 1_i * (! *tuple_selector) + 1_i * lit >= 1_i, ProofLevel::Current);
    }

    // tuple_selector may be null when proofs are disabled; the body only uses it inside
    // `if (logger)` branches (which are also the only branches that actually need it),
    // so passing nullptr is safe in that case and avoids forming a reference into an
    // empty pb_selectors vector at the call site.
    auto filter_edge(const SmartEntry & edge, VariableDomainMap & supported_by_tree, const ProofFlag * tuple_selector, const State & state,
        auto & inference, const ReasonLiterals &, ProofLogger * const logger) -> void
    {
        // Currently filter both domains - might be overkill
        // If the tree was in a better form, think this can be optimised to do less redundant filtering.
        overloaded{
            [&](const BinaryEntry & binary_entry) {
                vector<Integer> new_dom_1{};
                vector<Integer> new_dom_2{};

                auto dom_1 = get_for_actual_var(supported_by_tree, binary_entry.var_1);
                auto dom_2 = get_for_actual_var(supported_by_tree, binary_entry.var_2);
                sort(dom_1);
                sort(dom_2);

                switch (binary_entry.constraint_type) {
                    using enum SmartEntryConstraint;
                case LessThan:
                    copy_if(dom_2, back_inserter(new_dom_2), [&](Integer val) { return val > dom_1[0]; });
                    copy_if(dom_1, back_inserter(new_dom_1), [&](Integer val) { return val < dom_2[dom_2.size() - 1]; });
                    if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_2 >= (dom_1[0] + 1_i), state, inference,
                                singleton_reason(binary_entry.var_1 >= dom_1[0]));
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_1 < dom_2[dom_2.size() - 1], state, inference,
                                singleton_reason(binary_entry.var_2 < dom_2[dom_2.size() - 1] + 1_i));
                    }
                    break;
                case LessThanEqual:
                    copy_if(dom_2, back_inserter(new_dom_2), [&](Integer val) { return val >= dom_1[0]; });
                    copy_if(dom_1, back_inserter(new_dom_1), [&](Integer val) { return val <= dom_2[dom_2.size() - 1]; });
                    if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_2 >= (dom_1[0]), state, inference,
                                singleton_reason(binary_entry.var_1 >= dom_1[0]));
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_1 < (dom_2[dom_2.size() - 1] + 1_i), state, inference,
                                singleton_reason(binary_entry.var_2 < dom_2[dom_2.size() - 1] + 1_i));
                    }
                    break;
                case Equal:
                    set_intersection(dom_1, dom_2, back_inserter(new_dom_1));
                    new_dom_2 = new_dom_1;

                    if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                        // This one seems particularly annoying. Is it necessary? - not sure
                        if (new_dom_1.size() < dom_1.size()) {
                            vector<Integer> discarded_dom1;
                            set_difference(dom_1, dom_2, back_inserter(discarded_dom1));
                            for (const auto & val : discarded_dom1) {
                                log_filtering_inference(
                                    logger, tuple_selector, binary_entry.var_1 != val, state, inference, singleton_reason(binary_entry.var_2 != val));
                            }
                        }

                        if (new_dom_2.size() < dom_2.size()) {
                            vector<Integer> discarded_dom2;
                            set_difference(dom_2, dom_1, back_inserter(discarded_dom2));
                            for (const auto & val : discarded_dom2) {
                                log_filtering_inference(
                                    logger, tuple_selector, binary_entry.var_2 != val, state, inference, singleton_reason(binary_entry.var_1 != val));
                            }
                        }
                    }
                    break;
                case NotEqual:
                    if (dom_1.size() == 1) {
                        new_dom_1 = dom_1;
                        set_difference(dom_2, dom_1, back_inserter(new_dom_2));
                        if (logger && new_dom_2.size() < dom_2.size() && logger->get_assertion_level() == AssertionLevel::Off) {
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_2 != (dom_1[0]), state, inference,
                                singleton_reason(binary_entry.var_1 == dom_1[0]));
                        }
                    }
                    else if (dom_2.size() == 1) {
                        new_dom_2 = dom_2;
                        set_difference(dom_1, dom_2, back_inserter(new_dom_1));
                        if (logger && new_dom_1.size() < dom_1.size() && logger->get_assertion_level() == AssertionLevel::Off) {
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_1 != (dom_2[0]), state, inference,
                                singleton_reason(binary_entry.var_2 == dom_2[0]));
                        }
                    }
                    else {
                        new_dom_1 = move(dom_1);
                        new_dom_2 = move(dom_2);
                    }
                    break;
                case GreaterThan:
                    copy_if(dom_1, back_inserter(new_dom_1), [&](Integer val) { return val > dom_2[0]; });
                    copy_if(dom_2, back_inserter(new_dom_2), [&](Integer val) { return val < dom_1[dom_1.size() - 1]; });
                    if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_1 >= (dom_2[0] + 1_i), state, inference,
                                singleton_reason(binary_entry.var_2 >= dom_2[0]));
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_2 < dom_1[dom_1.size() - 1], state, inference,
                                singleton_reason(binary_entry.var_1 < dom_1[dom_1.size() - 1] + 1_i));
                    }
                    break;
                case GreaterThanEqual:
                    copy_if(dom_1, back_inserter(new_dom_1), [&](Integer val) { return val >= dom_2[0]; });
                    copy_if(dom_2, back_inserter(new_dom_2), [&](Integer val) { return val <= dom_1[dom_1.size() - 1]; });
                    if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                        if (new_dom_1.size() < dom_1.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_1 >= (dom_2[0]), state, inference,
                                singleton_reason(binary_entry.var_2 >= dom_2[0]));
                        if (new_dom_2.size() < dom_2.size())
                            log_filtering_inference(logger, tuple_selector, binary_entry.var_2 < (dom_1[dom_1.size() - 1] + 1_i), state, inference,
                                singleton_reason(binary_entry.var_1 < dom_1[dom_1.size() - 1] + 1_i));
                    }
                    break;
                default: throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                }
                set_for_actual_var(supported_by_tree, binary_entry.var_1, new_dom_1);
                set_for_actual_var(supported_by_tree, binary_entry.var_2, new_dom_2);
            }, //
            [&](const UnarySetEntry & unary_set_entry) {
                vector<Integer> new_dom{};
                auto dom = get_for_actual_var(supported_by_tree, unary_set_entry.var);
                auto set_values = unary_set_entry.values;
                sort(dom);
                sort(set_values);

                switch (unary_set_entry.constraint_type) {
                    using enum SmartEntryConstraint;
                case In: set_intersection(dom, set_values, back_inserter(new_dom)); break;
                case NotIn: set_difference(dom, set_values, back_inserter(new_dom)); break;
                default: throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                }

                set_for_actual_var(supported_by_tree, unary_set_entry.var, new_dom);
            }, //
            [&](const UnaryValueEntry & unary_val_entry) {
                vector<Integer> new_dom{};
                auto dom = get_for_actual_var(supported_by_tree, unary_val_entry.var);
                auto value = unary_val_entry.value;
                sort(dom);

                switch (unary_val_entry.constraint_type) {
                    using enum SmartEntryConstraint;
                case LessThan: copy_if(dom, back_inserter(new_dom), [&](Integer dom_val) { return dom_val < value; }); break;
                case LessThanEqual: copy_if(dom, back_inserter(new_dom), [&](Integer dom_val) { return dom_val <= value; }); break;
                case Equal: copy_if(dom, back_inserter(new_dom), [&](Integer dom_val) { return dom_val == value; }); break;
                case NotEqual: copy_if(dom, back_inserter(new_dom), [&](Integer dom_val) { return dom_val != value; }); break;
                case GreaterThan: copy_if(dom, back_inserter(new_dom), [&](Integer dom_val) { return dom_val > value; }); break;
                case GreaterThanEqual: copy_if(dom, back_inserter(new_dom), [&](Integer dom_val) { return dom_val >= value; }); break;
                default: throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                }

                set_for_actual_var(supported_by_tree, unary_val_entry.var, new_dom);
            } //
        }
            .visit(edge);
    }

    [[nodiscard]] auto filter_and_check_valid(const TreeEdges & tree, VariableDomainMap & supported_by_tree, const ProofFlag * tuple_selector,
        const State & state, auto & inference, const ReasonLiterals & reason, ProofLogger * const logger) -> bool
    {
        for (int l = tree.size() - 1; l >= 0; --l) {
            for (const auto & edge : tree[l]) {

                filter_edge(edge, supported_by_tree, tuple_selector, state, inference, reason, logger);

                bool domain_became_empty = false;
                overloaded{
                    [&](const BinaryEntry & binary_entry) {
                        if (get_for_actual_var(supported_by_tree, binary_entry.var_1).empty())
                            domain_became_empty = true;
                        if (get_for_actual_var(supported_by_tree, binary_entry.var_2).empty())
                            domain_became_empty = true;
                    }, //
                    [&](const UnarySetEntry & unary_set_entry) {
                        if (get_for_actual_var(supported_by_tree, unary_set_entry.var).empty())
                            domain_became_empty = true;
                    }, //
                    [&](const UnaryValueEntry & unary_val_entry) {
                        if (get_for_actual_var(supported_by_tree, unary_val_entry.var).empty())
                            domain_became_empty = true;
                    } //
                }
                    .visit(edge);

                if (domain_became_empty) {
                    return false;
                }
            }
        }
        return true;
    }

    // Both maps are keyed by the underlying variable, in its value space, so no
    // conversion through a view is needed here.
    auto remove_supported(VariableDomainMap & unsupported, const VariableDomainMap & supported_by_tree, const IntegerVariableID & var) -> void
    {
        auto actual_var = deview(var);
        vector<Integer> new_unsupported{};
        auto unsupported_set = set(unsupported.at(actual_var).begin(), unsupported.at(actual_var).end());
        auto to_remove_set = set(supported_by_tree.at(actual_var).begin(), supported_by_tree.at(actual_var).end());
        set_difference(unsupported_set, to_remove_set, back_inserter(new_unsupported));

        unsupported.at(actual_var) = move(new_unsupported);
    }

    auto filter_again_and_remove_supported(const TreeEdges & tree, VariableDomainMap & supported_by_tree, VariableDomainMap & unsupported,
        const ProofFlag * tuple_selector, const State & state, auto & inference, const ReasonLiterals & reason, ProofLogger * const logger) -> void
    {
        // The first pass went from the leaves up, so each node now holds only values
        // its own subtree supports, and the root is final. Going back down from the
        // root makes each child final in turn, which is GAC on the tree with no
        // iteration. A second pass from the leaves up would not: it filters each edge
        // before the edge above it has passed down the parent's final values, so a
        // restriction at the root gets only one level further down per pass.
        for (const auto & level : tree)
            for (const auto & edge : level)
                filter_edge(edge, supported_by_tree, tuple_selector, state, inference, reason, logger);

        // Only now is every node final, so only now can values be counted as supported.
        for (const auto & level : tree) {
            for (const auto & edge : level) {
                overloaded{
                    [&](const BinaryEntry & binary_entry) {
                        remove_supported(unsupported, supported_by_tree, binary_entry.var_1);
                        remove_supported(unsupported, supported_by_tree, binary_entry.var_2);
                    },                                                                                                                      //
                    [&](const UnarySetEntry & unary_set_entry) { remove_supported(unsupported, supported_by_tree, unary_set_entry.var); },  //
                    [&](const UnaryValueEntry & unary_val_entry) { remove_supported(unsupported, supported_by_tree, unary_val_entry.var); } //
                }
                    .visit(edge);
            }
        }
    }

    auto get_unrestricted(const vector<IntegerVariableID> & vars, const vector<SmartEntry> & tuple) -> vector<IntegerVariableID>
    {
        vector<IntegerVariableID> vars_in_tuple;
        vector<IntegerVariableID> unrestricted;
        for (const auto & entry : tuple) {
            overloaded{
                [&](const BinaryEntry & binary_entry) {
                    vars_in_tuple.emplace_back(deview(binary_entry.var_1));
                    vars_in_tuple.emplace_back(deview(binary_entry.var_2));
                },                                                                                                        //
                [&](const UnarySetEntry & unary_set_entry) { vars_in_tuple.emplace_back(deview(unary_set_entry.var)); },  //
                [&](const UnaryValueEntry & unary_val_entry) { vars_in_tuple.emplace_back(deview(unary_val_entry.var)); } //
            }
                .visit(entry);
        }

        set<IntegerVariableID> vars_set;
        for (const auto & var : vars)
            vars_set.emplace(deview(var));
        auto vars_in_tuple_set = set(vars_in_tuple.begin(), vars_in_tuple.end());

        set_difference(vars_set, vars_in_tuple_set, back_inserter(unrestricted));
        return unrestricted;
    }

    auto propagate_using_smart_str(const vector<IntegerVariableID> & selectors, const vector<IntegerVariableID> & vars, const SmartTuples & tuples,
        const vector<Forest> & forests, const State & state, auto & inference, const ReasonLiterals & reason, vector<ProofFlag> pb_selectors,
        ProofLogger * const logger, bool short_reasons, const ConstraintID & owner) -> void
    {
        // Everything in each underlying variable's current domain, keyed and valued
        // as a VariableDomainMap is. The same variable may appear more than once
        // in vars, possibly through different views, so seed each only once.
        VariableDomainMap current_domains{};
        for (const auto & var : vars) {
            auto actual_var = deview(var);
            if (! current_domains.contains(actual_var))
                for (auto value : state.each_value_immutable(actual_var))
                    current_domains[actual_var].emplace_back(value);
        }

        // Initialise unsupported values to everything in each variable's current domain.
        VariableDomainMap unsupported = current_domains;

        // Check that feasible tuples are still feasible
        // and also have them remove values from "unsupported" that they support
        for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
            // Skip infeasible tuple
            if (state.optional_single_value(selectors[tuple_idx]) == 0_i) {
                continue;
            }

            // pb_selectors is only populated when proof logging is enabled; index it
            // only in that case to avoid out-of-bounds access on an empty vector.
            const auto * pb_selector = logger ? &pb_selectors[tuple_idx] : nullptr;

            // A tuple supports nothing unless every one of its trees can still be
            // satisfied, so check them all before any of them takes values out of
            // unsupported. Otherwise a tree found valid first grants support on behalf
            // of a tuple that a later tree then kills, and since the selector is not a
            // trigger, nothing re-runs this to take it back (issue #994). The trees
            // are the tuple's connected components, so no tree's filtering reads
            // another's.
            const auto & forest = forests[tuple_idx];
            vector<VariableDomainMap> supported_by_trees;
            supported_by_trees.reserve(forest.size());
            bool tuple_feasible = true;
            for (const auto & tree : forest) {
                // Initialise supported by tree to current variable domains
                auto & supported_by_tree = supported_by_trees.emplace_back(current_domains);

                // First pass of filtering supported_by_tree and check of validity
                if (! filter_and_check_valid(tree, supported_by_tree, pb_selector, state, inference, reason, logger)) {
                    // Not feasible
                    inference.infer_equal(logger, selectors[tuple_idx], 0_i, NoJustificationNeeded{}, NoReason{});
                    tuple_feasible = false;
                    break;
                }
            }

            if (! tuple_feasible)
                continue;

            for (std::size_t tree_idx = 0; tree_idx < forest.size(); ++tree_idx)
                filter_again_and_remove_supported(
                    forest[tree_idx], supported_by_trees[tree_idx], unsupported, pb_selector, state, inference, reason, logger);

            const auto unrestricted = get_unrestricted(vars, tuples[tuple_idx]);
            for (const auto & var : unrestricted) {
                unsupported.at(var) = vector<Integer>{};
            }
        }

        bool some_tuple_still_feasible = false;
        for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
            if (state.optional_single_value(selectors[tuple_idx]) != 0_i) {
                some_tuple_still_feasible = true;
                break;
            }
        }

        auto unsupported_sum = WPBSum{};

        Reason reason_to_use;
        ProofLine reason_definition_1, reason_definition_2;
        if (logger && short_reasons) {
            auto reason_sum = WPBSum{};
            for (const auto & lit : reason) {
                reason_sum += 1_i * get<ProofLiteral>(lit);
            }
            // We will manually delete this later.
            auto [_reason_short, _line1, _line2] =
                logger->create_proof_flag_reifying(reason_sum >= Integer(reason_sum.terms.size()), "sr", ProofLevel::Top);
            ProofFlag reason_short = _reason_short;
            reason_definition_1 = _line1;
            reason_definition_2 = _line2;
            reason_to_use = singleton_reason(reason_short);
        }
        else {
            reason_to_use = reason;
        }

        if (! some_tuple_still_feasible) {
            if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
                auto justf = [&](const ReasonLiterals & reason) -> void {
                    for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
                        logger->emit_rup_proof_line_under_reason(reason, WPBSum{} + 1_i * (! pb_selectors[tuple_idx]) >= 1_i, ProofLevel::Temporary);
                    }
                };
                inference.contradiction(logger, JustifyExplicitly{justf, ThenRUP::Yes, hints::SmartTable{owner}}, reason_to_use);
                // if (short_reasons) {
                //     logger->delete_range(reason_definition_1, reason_definition_2 + 1);
                // }
            }
            else {
                inference.contradiction(logger, JustifyUsingRUP{hints::SmartTable{owner}}, reason);
            }
            return;
        }
        // Infer each removal on the variable as vars names it, converting the value
        // back through the view, and only once per underlying variable.
        vector<pair<IntegerVariableID, Integer>> removals;
        set<IntegerVariableID> removed_from;
        for (const auto & var : vars)
            if (removed_from.emplace(deview(var)).second)
                for (const auto & value : unsupported.at(deview(var)))
                    removals.emplace_back(var, to_view_value(var, value));

        if (logger && logger->get_assertion_level() == AssertionLevel::Off) {
            for (const auto & [var, value] : removals) {
                auto justf = [&](const ReasonLiterals & reason) -> void {
                    for (unsigned int tuple_idx = 0; tuple_idx < tuples.size(); ++tuple_idx) {
                        logger->emit_rup_proof_line_under_reason(
                            reason, WPBSum{} + 1_i * (var != value) + 1_i * (! pb_selectors[tuple_idx]) >= 1_i, ProofLevel::Temporary);
                    }
                };
                inference.infer_not_equal(logger, var, value, JustifyExplicitly{justf, ThenRUP::Yes, hints::SmartTable{owner}}, reason_to_use);
            }
            // if (short_reasons) {
            //     logger->delete_range(reason_definition_1, reason_definition_2 + 1);
            // }
        }
        else {
            for (const auto & [var, value] : removals)
                inference.infer_not_equal(logger, var, value, JustifyUsingRUP{hints::SmartTable{owner}}, NoReason{});
        }
    }

    auto build_tree(const IntegerVariableID & root, int current_level, vector<vector<SmartEntry>> & entry_tree,
        unordered_map<IntegerVariableID, bool> & node_visited, const unordered_map<IntegerVariableID, vector<SmartEntry>> & adjacent_edges) -> void
    {
        node_visited[deview(root)] = true;

        // Simple recursive traverse
        // Note: Perhaps we should build the tree in a "smarter" form e.g. make sure var_1 is always the node
        //       closer to the root.
        for (const auto & edge : adjacent_edges.at(deview(root))) {
            overloaded{
                [&](BinaryEntry binary_entry) {
                    if (! node_visited[deview(binary_entry.var_1)]) {
                        entry_tree[current_level].emplace_back(edge);
                        entry_tree.emplace_back();

                        build_tree(binary_entry.var_1, current_level + 1, entry_tree, node_visited, adjacent_edges);
                    }
                    else if (! node_visited[deview(binary_entry.var_2)]) {
                        entry_tree[current_level].emplace_back(edge);
                        entry_tree.emplace_back();
                        build_tree(binary_entry.var_2, current_level + 1, entry_tree, node_visited, adjacent_edges);
                    }
                },                                                                             //
                [&](const UnarySetEntry &) { entry_tree[current_level].emplace_back(edge); },  //
                [&](const UnaryValueEntry &) { entry_tree[current_level].emplace_back(edge); } //
            }
                .visit(edge);
        }
    }

    [[nodiscard]] auto build_forests(SmartTuples & tuples) -> vector<Forest>
    {
        vector<Forest> forests{};
        for (const auto & current_tuple : tuples) {
            unordered_map<IntegerVariableID, bool> node_visited;
            unordered_map<IntegerVariableID, vector<SmartEntry>> adjacent_edges;

            // Get all the vars in the tuple and record adjacencies
            for (const auto & entry : current_tuple) {
                overloaded{
                    [&](const BinaryEntry & binary_entry) {
                        node_visited[deview(binary_entry.var_1)] = false;
                        node_visited[deview(binary_entry.var_2)] = false;
                        adjacent_edges[deview(binary_entry.var_1)].emplace_back(binary_entry);
                        adjacent_edges[deview(binary_entry.var_2)].emplace_back(binary_entry);
                    }, //
                    [&](const UnaryValueEntry & unary_val_entry) {
                        node_visited[deview(unary_val_entry.var)] = false;
                        adjacent_edges[deview(unary_val_entry.var)].emplace_back(unary_val_entry);
                    }, //
                    [&](const UnarySetEntry & unary_set_entry) {
                        node_visited[deview(unary_set_entry.var)] = false;
                        adjacent_edges[deview(unary_set_entry.var)].emplace_back(unary_set_entry);
                    } //
                }
                    .visit(entry);
            }

            // Root the trees in the order their variables first appear in the tuple,
            // not in node_visited's order, which differs between standard libraries.
            vector<IntegerVariableID> vars_in_order;
            for (const auto & entry : current_tuple)
                overloaded{//
                    [&](const BinaryEntry & binary_entry) {
                        vars_in_order.emplace_back(deview(binary_entry.var_1));
                        vars_in_order.emplace_back(deview(binary_entry.var_2));
                    },
                    [&](const UnaryValueEntry & unary_val_entry) { vars_in_order.emplace_back(deview(unary_val_entry.var)); },
                    [&](const UnarySetEntry & unary_set_entry) { vars_in_order.emplace_back(deview(unary_set_entry.var)); }}
                    .visit(entry);

            Forest forest{};
            for (const auto & var : vars_in_order) {
                if (node_visited.at(var))
                    continue;
                vector<vector<SmartEntry>> entry_tree;
                entry_tree.emplace_back();
                // Recursively build the tree starting from this node
                build_tree(var, 0, entry_tree, node_visited, adjacent_edges);
                forest.emplace_back(entry_tree);
            }

            forests.emplace_back(forest);
        }
        return forests;
    }

    // For PB model
    [[nodiscard]] auto make_binary_entry_flag(
        ProofModel & model, const IntegerVariableID & var_1, const IntegerVariableID & var_2, const SmartEntryConstraint & c) -> ProofFlag
    {
        switch (c) {
            using enum SmartEntryConstraint;
        case Equal: {
            // f => var1 == var2
            auto flag = model.create_proof_flag("bin_eq");
            model.add_constraint(WPBSum{} + 1_i * var_1 + -1_i * var_2 == 0_i, HalfReifyOnConjunctionOf{{flag}});

            // !f => var1 != var2 via fully reified lt/gt and a selector
            auto flag_gt = model.create_proof_flag_fully_reifying("gt", WPBSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i);
            auto flag_lt = model.create_proof_flag_fully_reifying("lt", WPBSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i);
            model.add_constraint(WPBSum{} + 1_i * flag_lt + 1_i * flag_gt >= 1_i, HalfReifyOnConjunctionOf{{! flag}});
            return flag;
        }

        case GreaterThan: return model.create_proof_flag_fully_reifying("bin_gt", WPBSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i);

        case LessThan: return model.create_proof_flag_fully_reifying("bin_lt", WPBSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i);

        case LessThanEqual: return model.create_proof_flag_fully_reifying("bin_le", WPBSum{} + 1_i * var_2 + -1_i * var_1 >= 0_i);

        case NotEqual: {
            // !f => var1 == var2
            auto flag = model.create_proof_flag("bin_eq");
            model.add_constraint(WPBSum{} + 1_i * var_1 + -1_i * var_2 == 0_i, HalfReifyOnConjunctionOf{{! flag}});

            // f => var1 != var2, via fully reified lt/gt and a selector
            auto flag_gt = model.create_proof_flag_fully_reifying("gt", WPBSum{} + 1_i * var_1 + -1_i * var_2 >= 1_i);
            auto flag_lt = model.create_proof_flag_fully_reifying("lt", WPBSum{} + 1_i * var_2 + -1_i * var_1 >= 1_i);
            model.add_constraint(WPBSum{} + 1_i * flag_lt + 1_i * flag_gt >= 1_i, HalfReifyOnConjunctionOf{{flag}});

            return flag;
        }

        case GreaterThanEqual: return model.create_proof_flag_fully_reifying("bin_ge", WPBSum{} + 1_i * var_1 + -1_i * var_2 >= 0_i);

        case NotIn:
        case In: throw UnexpectedException{"Unexpected SmartEntry type encountered while creating PB model."};
        }
        throw NonExhaustiveSwitch{};
    }

    auto literal_from_unary_entry(UnaryValueEntry & unary_entry) -> Literal
    {
        auto var = unary_entry.var;
        auto value = unary_entry.value;
        switch (unary_entry.constraint_type) {
            using enum SmartEntryConstraint;
        case LessThan: return var < value;
        case LessThanEqual: return var <= value;
        case Equal: return var == value;
        case NotEqual: return var != value;
        case GreaterThan: return var > value;
        case GreaterThanEqual: return var >= value;
        case In:
        case NotIn: throw UnexpectedException{"Unexpected SmartEntry type encountered while creating PB model."};
        }
        throw NonExhaustiveSwitch{};
    }
}

auto provable_entry_member(IntegerVariableID v) -> bool
{
    return overloaded{
        [&](ViewOfIntegerVariableID & v) -> bool { return ! v.negate_first && v.then_add >= 0_i; }, //
        [&](ConstantIntegerVariableID) -> bool { return false; },                                   //
        [&](SimpleIntegerVariableID) -> bool { return true; }                                       //
    }
        .visit(v);
}

auto consolidate_unary_entries(const State & state, vector<SmartEntry> tuple) -> vector<SmartEntry>
{
    // TODO:
    //  Using an IntervalSet data structure we could do this in a much better way, but this
    //  will do for now
    map<IntegerVariableID, vector<SmartEntry>> unary_entries{};
    vector<SmartEntry> new_tuple{};
    for (const auto & entry : tuple) {
        overloaded{
            [&](BinaryEntry binary_entry) { new_tuple.emplace_back(binary_entry); }, //
            [&](UnaryValueEntry value_entry) {
                auto & entries = unary_entries[value_entry.var];
                entries.emplace_back(value_entry);
            }, //
            [&](UnarySetEntry set_entry) {
                auto & entries = unary_entries[set_entry.var];
                entries.emplace_back(set_entry);
            } //
        }
            .visit(entry);
    }

    for (auto & var_and_entries : unary_entries) {
        const auto & var = var_and_entries.first;
        const auto & entries = var_and_entries.second;
        vector<Integer> allowed_vals{};

        for (auto v : state.each_value_immutable(var)) {
            bool val_allowed = true;
            for (auto & entry : entries) {
                overloaded{
                    [&](BinaryEntry) { throw UnexpectedException{"Shouldn't have a binary entry here."}; }, //
                    [&](UnaryValueEntry value_entry) {
                        switch (value_entry.constraint_type) {
                        case SmartEntryConstraint::LessThan: val_allowed = val_allowed && v < value_entry.value; break;
                        case SmartEntryConstraint::LessThanEqual: val_allowed = val_allowed && v <= value_entry.value; break;
                        case SmartEntryConstraint::Equal: val_allowed = val_allowed && v == value_entry.value; break;
                        case SmartEntryConstraint::NotEqual: val_allowed = val_allowed && v != value_entry.value; break;
                        case SmartEntryConstraint::GreaterThan: val_allowed = val_allowed && v > value_entry.value; break;
                        case SmartEntryConstraint::GreaterThanEqual: val_allowed = val_allowed && v >= value_entry.value; break;
                        case SmartEntryConstraint::In:
                        case SmartEntryConstraint::NotIn: throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                        }
                    }, //
                    [&](UnarySetEntry set_entry) {
                        switch (set_entry.constraint_type) {
                        case SmartEntryConstraint::In:
                            val_allowed = val_allowed && std::count(set_entry.values.begin(), set_entry.values.end(), v);
                            break;
                        case SmartEntryConstraint::NotIn:
                            val_allowed = val_allowed && ! std::count(set_entry.values.begin(), set_entry.values.end(), v);
                            break;
                        case SmartEntryConstraint::LessThan:
                        case SmartEntryConstraint::LessThanEqual:
                        case SmartEntryConstraint::Equal:
                        case SmartEntryConstraint::NotEqual:
                        case SmartEntryConstraint::GreaterThan:
                        case SmartEntryConstraint::GreaterThanEqual: throw UnexpectedException{"Unexpected SmartEntry type encountered."};
                        }
                    } //
                }
                    .visit(entry);
            }
            if (val_allowed) {
                allowed_vals.emplace_back(v);
            }
        }

        auto new_entry_for_var = SmartTable::in_set(var, allowed_vals);
        new_tuple.emplace_back(new_entry_for_var);
    }
    return new_tuple;
}

auto SmartTable::with_short_reasons(std::optional<bool> short_reasons) -> SmartTable &
{
    _short_reasons = short_reasons.value_or(true);
    return *this;
}

auto SmartTable::clone() const -> unique_ptr<Constraint>
{
    auto cloned = make_unique<SmartTable>(_vars, _tuples);
    cloned->with_short_reasons(_short_reasons);
    return cloned;
}

auto SmartTable::prepare(Propagators &, State & initial_state, ProofModel * const) -> bool
{
    // One 0/1 selector variable per tuple: allocating is a prepare() job.
    for (unsigned int i = 0; i < _tuples.size(); ++i)
        _selectors.emplace_back(initial_state.allocate_integer_variable_with_state(0_i, 1_i));

    return true;
}

auto SmartTable::define_proof_model(ProofModel & model, const State & initial_state) -> void
{
    auto & pb_selectors = _pb_selectors;

    for (unsigned int i = 0; i < _tuples.size(); ++i) {
        pb_selectors.emplace_back(model.create_proof_flag(format("t{}", i)));
    }
    WPBSum sum_pb_selectors{};

    for (const auto & s : pb_selectors)
        sum_pb_selectors += 1_i * s;

    model.add_constraint(sum_pb_selectors >= 1_i);

    // Would need a hash function for unordered map, but this shouldn't be too slow
    map<BinaryEntryData, ProofFlag> smart_entry_flags;

    for (unsigned int tuple_idx = 0; tuple_idx < _tuples.size(); ++tuple_idx) {
        WPBSum entry_flags_sum{};
        WPBSum entry_flags_neg_sum{};
        for (const auto & entry : consolidate_unary_entries(initial_state, _tuples[tuple_idx])) {
            overloaded{
                [&](BinaryEntry binary_entry) {
                    //                        if(!provable_entry_member(binary_entry.var_1) || !provable_entry_member(binary_entry.var_2)) {
                    //                            throw UnimplementedException{"Can only proof log smart table binary entries of form <var> <op> <var> + b where b >= 0."};
                    //                        }
                    auto binary_entry_data = make_tuple(binary_entry.var_1, binary_entry.var_2, binary_entry.constraint_type);
                    if (! smart_entry_flags.contains(binary_entry_data))
                        smart_entry_flags[binary_entry_data] =
                            make_binary_entry_flag(model, binary_entry.var_1, binary_entry.var_2, binary_entry.constraint_type);

                    entry_flags_sum += 1_i * smart_entry_flags[binary_entry_data];
                    entry_flags_neg_sum += -1_i * smart_entry_flags[binary_entry_data];
                }, //
                [&](const UnarySetEntry & unary_set_entry) {
                    auto var = unary_set_entry.var;
                    auto flag = unary_set_entry.constraint_type == SmartEntryConstraint::In ? model.create_proof_flag("inset")
                                                                                            : model.create_proof_flag("notinset");

                    // InSet {<empty>} is the same as False
                    if (unary_set_entry.values.empty() && unary_set_entry.constraint_type == SmartEntryConstraint::In) {
                        model.add_constraint(WPBSum{} + 1_i * ! flag >= 1_i);
                        entry_flags_sum += 1_i * flag;
                        entry_flags_neg_sum += -1_i * flag;
                        return;
                    }
                    WPBSum set_value_sum{};
                    WPBSum neg_set_value_sum{};
                    for (auto val : initial_state.each_value_immutable(var)) {
                        if (! count(unary_set_entry.values.begin(), unary_set_entry.values.end(), val))
                            set_value_sum += 1_i * (var != val);
                    }

                    for (const auto & val : unary_set_entry.values)
                        neg_set_value_sum += 1_i * (var != val);

                    auto set_rhs = Integer{static_cast<long long>(set_value_sum.terms.size())};
                    auto neg_set_rhs = Integer{static_cast<long long>(neg_set_value_sum.terms.size())};
                    model.add_constraint(move(set_value_sum) >= set_rhs,
                        HalfReifyOnConjunctionOf{{unary_set_entry.constraint_type == SmartEntryConstraint::In ? flag : ! flag}});
                    model.add_constraint(move(neg_set_value_sum) >= neg_set_rhs,
                        HalfReifyOnConjunctionOf{{unary_set_entry.constraint_type == SmartEntryConstraint::In ? ! flag : flag}});

                    entry_flags_sum += 1_i * flag;
                    entry_flags_neg_sum += -1_i * flag;
                }, //
                [&](UnaryValueEntry unary_value_entry) {
                    Literal l = literal_from_unary_entry(unary_value_entry);
                    entry_flags_sum += 1_i * l;
                    entry_flags_neg_sum += -1_i * l;
                } //
            }
                .visit(entry);
        }
        auto tuple_len = Integer{static_cast<long long>(entry_flags_sum.terms.size())};
        model.add_constraint(move(entry_flags_sum) >= tuple_len, HalfReifyOnConjunctionOf{{pb_selectors[tuple_idx]}});
        model.add_constraint(move(entry_flags_neg_sum) >= -tuple_len + 1_i, HalfReifyOnConjunctionOf{{! pb_selectors[tuple_idx]}});
    }
}

auto SmartTable::install_propagators(Propagators & propagators) -> void
{
    // Trigger when any var changes? Is this over-kill?
    Triggers triggers;
    triggers.on_change = {_vars.begin(), _vars.end()};

    vector<Forest> forests = build_forests(_tuples);

    propagators.install(
        constraint_id(),
        [selectors = _selectors, vars = _vars, tuples = move(_tuples), forests = move(forests), pb_selectors = move(_pb_selectors),
            short_reasons = _short_reasons,
            owner = constraint_id()](const State & state, auto & inference, ProofLogger * const logger) -> PropagatorState {
            auto reason = eager_reason(generic_reason(vars), state);
            propagate_using_smart_str(selectors, vars, tuples, forests, state, inference, reason, pb_selectors, logger, short_reasons, owner);
            return PropagatorState::Enable;
        },
        triggers);
}

auto SmartTable::constraint_type() const -> std::string
{
    return "smart_table";
}

auto SmartTable::s_expr(const ProofModel * const model) const -> SExpr
{
    auto to_op = [](SmartEntryConstraint c) {
        switch (c) {
        case SmartEntryConstraint::LessThan: return "<";
        case SmartEntryConstraint::LessThanEqual: return "<=";
        case SmartEntryConstraint::Equal: return "=";
        case SmartEntryConstraint::NotEqual: return "!=";
        case SmartEntryConstraint::GreaterThan: return ">";
        case SmartEntryConstraint::GreaterThanEqual: return ">=";
        case SmartEntryConstraint::In: return "in";
        case SmartEntryConstraint::NotIn: return "notin";
        }
        throw NonExhaustiveSwitch{};
    };

    auto & tracker = model->names_and_ids_tracker();

    // Each tuple is one row of the table (a conjunction of entries); keep the rows
    // delimited so the disjunction structure stays recoverable downstream (and
    // matches the row-delimited form cake_pb_cp's parser expects).
    vector<SExpr> rows;
    for (const auto & tuple : _tuples) {
        vector<SExpr> entries;
        for (const auto & entry : tuple) {
            overloaded{
                [&](const BinaryEntry & binary_entry) {
                    entries.push_back(SExpr::list({tracker.s_expr_term_of(binary_entry.var_1), SExpr::atom(to_op(binary_entry.constraint_type)),
                        tracker.s_expr_term_of(binary_entry.var_2)}));
                }, //
                [&](const UnaryValueEntry & unary_val_entry) {
                    entries.push_back(SExpr::list({tracker.s_expr_term_of(unary_val_entry.var), SExpr::atom(to_op(unary_val_entry.constraint_type)),
                        SExpr::atom(unary_val_entry.value.to_string())}));
                }, //
                [&](const UnarySetEntry & unary_set_entry) {
                    vector<SExpr> values;
                    for (const auto & value : unary_set_entry.values)
                        values.push_back(SExpr::atom(value.to_string()));
                    entries.push_back(SExpr::list({tracker.s_expr_term_of(unary_set_entry.var), SExpr::atom(to_op(unary_set_entry.constraint_type)),
                        SExpr::list(move(values))}));
                } //
            }
                .visit(entry);
        }
        rows.push_back(SExpr::list(move(entries)));
    }

    vector<SExpr> vars;
    for (const auto & var : _vars)
        vars.push_back(tracker.s_expr_term_of(var));

    return SExpr::list({SExpr::atom(as_string(_constraint_id)), SExpr::atom(constraint_type()), SExpr::list(move(rows)), SExpr::list(move(vars))});
}
