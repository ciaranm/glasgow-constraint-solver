#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INCREASING_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_INCREASING_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    /**
     * \brief General implementation for Increasing, StrictlyIncreasing,
     * Decreasing, and StrictlyDecreasing.
     *
     * Achieves bounds consistency in a single forward+backward sweep, which
     * is more efficient than the equivalent chain of binary inequality
     * constraints (where bound updates would have to ripple along the chain
     * via the propagation queue, one step at a time).
     *
     * \ingroup Constraints
     * \ingroup Innards
     * \sa Increasing
     * \sa StrictlyIncreasing
     * \sa Decreasing
     * \sa StrictlyDecreasing
     */
    class IncreasingChain : public Constraint
    {
    private:
        std::vector<IntegerVariableID> _vars;
        bool _strict;
        bool _descending;

    public:
        explicit IncreasingChain(std::vector<IntegerVariableID> vars, bool strict, bool descending);

        virtual auto install(innards::Propagators &, innards::State &,
            innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
        [[nodiscard]] virtual auto s_exprify(const std::string & name, const innards::ProofModel * const) const -> std::string override;
    };

    /**
     * \brief Constrain that vars[0] <= vars[1] <= ... <= vars[n-1].
     *
     * \ingroup Constraints
     */
    class Increasing : public IncreasingChain
    {
    public:
        inline explicit Increasing(std::vector<IntegerVariableID> vars) :
            IncreasingChain(std::move(vars), false, false) {};
    };

    /**
     * \brief Constrain that vars[0] < vars[1] < ... < vars[n-1].
     *
     * \ingroup Constraints
     */
    class StrictlyIncreasing : public IncreasingChain
    {
    public:
        inline explicit StrictlyIncreasing(std::vector<IntegerVariableID> vars) :
            IncreasingChain(std::move(vars), true, false) {};
    };

    /**
     * \brief Constrain that vars[0] >= vars[1] >= ... >= vars[n-1].
     *
     * \ingroup Constraints
     */
    class Decreasing : public IncreasingChain
    {
    public:
        inline explicit Decreasing(std::vector<IntegerVariableID> vars) :
            IncreasingChain(std::move(vars), false, true) {};
    };

    /**
     * \brief Constrain that vars[0] > vars[1] > ... > vars[n-1].
     *
     * \ingroup Constraints
     */
    class StrictlyDecreasing : public IncreasingChain
    {
    public:
        inline explicit StrictlyDecreasing(std::vector<IntegerVariableID> vars) :
            IncreasingChain(std::move(vars), true, true) {};
    };
}

#endif
