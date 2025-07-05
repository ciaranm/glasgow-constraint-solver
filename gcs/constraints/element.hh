#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_ELEMENT_HH

#include <gcs/constraint.hh>
#include <gcs/variable_id.hh>

#include <vector>

namespace gcs
{
    namespace innards
    {
        template <typename E_, unsigned n_>
        struct MakeNDVector;

        template <typename E_>
        struct MakeNDVector<E_, 1>
        {
            using Type = std::vector<E_>;
        };

        template <typename E_, unsigned n_>
        struct MakeNDVector
        {
            using Type = std::vector<typename MakeNDVector<E_, n_ - 1>::Type>;
        };
    }

    template <typename EntryType_, unsigned dimensions_>
    class NDimensionalElement : public Constraint
    {
    public:
        using Array = const innards::MakeNDVector<EntryType_, dimensions_>::Type;
        using IndexVariables = std::vector<IntegerVariableID>;
        using IndexStarts = std::vector<Integer>;

    private:
        IntegerVariableID _result_var;
        IndexVariables _index_vars;
        IndexStarts _index_starts;
        Array * _array;
        bool _bounds_only;

    protected:
        explicit NDimensionalElement(IntegerVariableID result_var, IndexVariables, IndexStarts, Array *, bool bounds_only);

    public:
        virtual auto install(innards::Propagators &, innards::State &, innards::ProofModel * const) && -> void override;
        virtual auto clone() const -> std::unique_ptr<Constraint> override;
    };

    class Element : public NDimensionalElement<IntegerVariableID, 1>
    {
    public:
        explicit Element(IntegerVariableID var, IntegerVariableID zero_idx, Array * array, bool bounds_only = false) :
            NDimensionalElement(var, {{zero_idx}}, {{0_i}}, array, bounds_only)
        {
        }

        explicit Element(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx, Array * array, bool bounds_only = false) :
            NDimensionalElement(var, {{idx.first}}, {{idx.second}}, array, bounds_only)
        {
        }
    };

    class Element2D : public NDimensionalElement<IntegerVariableID, 2>
    {
    public:
        explicit Element2D(IntegerVariableID var, IntegerVariableID zero_idx_1, IntegerVariableID zero_idx_2, Array * array, bool bounds_only = false) :
            NDimensionalElement(var, {{zero_idx_1, zero_idx_2}}, {{0_i, 0_i}}, array, bounds_only)
        {
        }

        explicit Element2D(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx1, std::pair<IntegerVariableID, Integer> idx2, Array * array, bool bounds_only = false) :
            NDimensionalElement(var, {{idx1.first, idx2.first}}, {{idx1.second, idx2.second}}, array, bounds_only)
        {
        }
    };

    class ElementConstantArray : public NDimensionalElement<Integer, 1>
    {
    public:
        explicit ElementConstantArray(IntegerVariableID var, IntegerVariableID zero_idx, Array * array, bool bounds_only = true) :
            NDimensionalElement(var, {{zero_idx}}, {{0_i}}, array, bounds_only)
        {
        }

        explicit ElementConstantArray(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx, Array * array, bool bounds_only = true) :
            NDimensionalElement(var, {{idx.first}}, {{idx.second}}, array, bounds_only)
        {
        }
    };

    class Element2DConstantArray : public NDimensionalElement<Integer, 2>
    {
    public:
        explicit Element2DConstantArray(IntegerVariableID var, IntegerVariableID idx1, IntegerVariableID idx2, Array * array, bool bounds_only = true) :
            NDimensionalElement(var, {{idx1, idx2}}, {{0_i, 0_i}}, array, bounds_only)
        {
        }

        explicit Element2DConstantArray(IntegerVariableID var, std::pair<IntegerVariableID, Integer> idx1, std::pair<IntegerVariableID, Integer> idx2, Array * array, bool bounds_only = true) :
            NDimensionalElement(var, {{idx1.first, idx2.first}}, {{idx1.second, idx2.second}}, array, bounds_only)
        {
        }
    };
}

#endif
