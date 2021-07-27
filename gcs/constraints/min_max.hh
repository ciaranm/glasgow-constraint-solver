/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MIN_MAX_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_CONSTRAINTS_MIN_MAX_HH 1

#include <gcs/constraint.hh>
#include <gcs/integer_variable.hh>

namespace gcs
{
    class ArrayMinMax :
        public Constraint
    {
        private:
            const std::vector<IntegerVariableID> & _vars;
            IntegerVariableID _result;
            bool _min;

        public:
            explicit ArrayMinMax(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result, bool min);

            virtual auto convert_to_low_level(LowLevelConstraintStore &, const State &) && -> void override;
    };

    class Min :
        public ArrayMinMax
    {
        private:
            std::vector<IntegerVariableID> _vs;

        public:
            explicit Min(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);
    };

    class Max :
        public ArrayMinMax
    {
        private:
            std::vector<IntegerVariableID> _vs;

        public:
            explicit Max(const IntegerVariableID v1, const IntegerVariableID v2, const IntegerVariableID result);
    };

    class ArrayMin :
        public ArrayMinMax
    {
        public:
            explicit ArrayMin(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result);
    };

    class ArrayMax :
        public ArrayMinMax
    {
        public:
            explicit ArrayMax(const std::vector<IntegerVariableID> & vars, const IntegerVariableID result);
    };
}

#endif
