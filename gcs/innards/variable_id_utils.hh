#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_VARIABLE_ID_UTILS_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_INNARDS_VARIABLE_ID_UTILS_HH

#include <gcs/variable_id.hh>

#include <concepts>
#include <string>
#include <utility>

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
     * Convert an IntegerVariableID into a roughly-readable string, for debugging.
     *
     * \ingroup Innards
     */
    [[nodiscard]] auto debug_string(const IntegerVariableID &) -> std::string;
}

#endif
