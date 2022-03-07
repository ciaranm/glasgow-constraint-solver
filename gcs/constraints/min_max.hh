/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MIN_MAX_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MIN_MAX_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    namespace innards
    {
        /**
         * \brief Constrain that result is either the minimum or maximum of the
         * specified variables.
         *
         * \ingroup Constraints
         * \ingroup Innards
         * \sa Min
         * \sa Max
         * \sa ArrayMin
         * \sa ArrayMax
         */
        class ArrayMinMax : public Constraint
        {
        private:
            const std::vector<IntegerVariableID> & _vars;
            IntegerVariableID _result;
            bool _min;

        public:
            explicit ArrayMinMax(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result, bool min);

            virtual auto describe_for_proof() -> std::string override;
            virtual auto install(innards::Propagators &, const innards::State &) && -> void override;
        };
    }

    /**
     * \brief Constrain that the minimum of the two values is equal to the
     * result.
     *
     * \ingroup Constraints
     * \sa Max
     * \sa ArrayMin
     */
    class Min : public innards::ArrayMinMax
    {
    private:
        std::vector<IntegerVariableID> _vs;

    public:
        explicit Min(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);
    };

    /**
     * \brief Constrain that the maximum of the two values is equal to the
     * result.
     *
     * \ingroup Constraints
     * \sa Min
     * \sa ArrayMax
     */
    class Max : public innards::ArrayMinMax
    {
    private:
        std::vector<IntegerVariableID> _vs;

    public:
        explicit Max(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);
    };

    /**
     * \brief Constrain that the minimum of the array of values is equal to the
     * result.
     *
     * \ingroup Constraints
     * \sa Min
     * \sa ArrayMax
     */
    class ArrayMin : public innards::ArrayMinMax
    {
    public:
        explicit ArrayMin(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result);
    };

    /**
     * \brief Constrain that the maximum of the array of values is equal to the
     * result.
     *
     * \ingroup Constraints
     * \sa Max
     * \sa ArrayMin
     */
    class ArrayMax : public innards::ArrayMinMax
    {
    public:
        explicit ArrayMax(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result);
    };
}

#endif
