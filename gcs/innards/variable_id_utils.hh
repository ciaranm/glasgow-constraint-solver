#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_VARIABLE_ID_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_VARIABLE_ID_UTILS_HH

#include <gcs/variable_id.hh>

#include <algorithm>
#include <concepts>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace gcs::innards
{
    /**
     * \brief Either an IntegerVariableID, or one of its more specific types.
     *
     * \ingroup Innards
     */
    template <typename T_>
    concept IntegerVariableIDLike = std::is_convertible_v<T_, IntegerVariableID>;

    /**
     * \brief An IntegerVariableID that isn't a view.
     *
     * \ingroup Innards
     */
    using DirectIntegerVariableID = std::variant<SimpleIntegerVariableID, ConstantIntegerVariableID>;

    /**
     * \brief Either a DirectIntegerVariableID, or one of its more specific types.
     *
     * \ingroup Innards
     */
    template <typename T_>
    concept DirectIntegerVariableIDLike = std::is_convertible_v<T_, DirectIntegerVariableID>;

    /**
     * \brief The result of as_homogeneous(): a vector specialised to one concrete
     * IntegerVariableID alternative, or the general mixed vector.
     *
     * \ingroup Innards
     */
    using HomogeneousIntegerVariables = std::variant<std::vector<SimpleIntegerVariableID>, std::vector<ConstantIntegerVariableID>,
        std::vector<ViewOfIntegerVariableID>, std::vector<IntegerVariableID>>;

    namespace detail
    {
        template <typename T_, typename Container_>
        [[nodiscard]] auto extract_homogeneous(const Container_ & vars) -> std::vector<T_>
        {
            std::vector<T_> result;
            result.reserve(vars.size());
            for (const auto & v : vars)
                result.push_back(std::get<T_>(v));
            return result;
        }
    }

    /**
     * \brief If every entry of \p vars is the same IntegerVariableID alternative,
     * return a vector of that concrete type; otherwise return the mixed vector
     * unchanged.
     *
     * Accepts any container of IntegerVariableID (e.g. std::vector or small_vector):
     * it is templated on the container as a whole, deducing the element type, rather
     * than taking a template-template parameter -- the latter would not bind to
     * small_vector, whose signature carries a non-type inline-capacity parameter. The
     * result is always a std::vector of the concrete type (one install-time
     * allocation), not a rebind of the input container kind.
     *
     * std::visit the result to dispatch a computation onto a single homogeneous
     * specialisation -- so e.g. per-element domain iteration takes the trivial
     * same-type path rather than a variant visit -- falling back to the general
     * IntegerVariableID path only for genuinely mixed scopes. An empty scope yields
     * the (empty) mixed vector.
     *
     * \ingroup Innards
     */
    template <typename Container_>
        requires std::same_as<typename Container_::value_type, IntegerVariableID>
    [[nodiscard]] auto as_homogeneous(const Container_ & vars) -> HomogeneousIntegerVariables
    {
        if (! vars.empty()) {
            auto first = vars.front().index();
            if (std::all_of(vars.begin(), vars.end(), [&](const IntegerVariableID & v) { return v.index() == first; }))
                // Recover the concrete alternative type by visiting the first
                // entry, rather than mapping raw variant indices to types by hand.
                return std::visit(
                    [&](const auto & first_var) -> HomogeneousIntegerVariables {
                        return detail::extract_homogeneous<std::decay_t<decltype(first_var)>>(vars);
                    },
                    vars.front());
        }
        return std::vector<IntegerVariableID>(vars.begin(), vars.end());
    }

    /**
     * Convert an IntegerVariableID into a roughly-readable string, for debugging.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto debug_string(const IntegerVariableID &) -> std::string;
}

#endif
