#include <gcs/innards/propagators.hh>
#include <gcs/innards/state.hh>
#include <gcs/problem.hh>
#include <gcs/solve.hh>

#include <iostream>
#include <string>

#include <boost/program_options.hpp>

using namespace gcs;
using namespace innards;

using std::cerr;
using std::cout;
using std::endl;
using std::make_optional;
using std::nullopt;
using std::pair;
using std::string;
using std::unique_ptr;
using std::vector;

class Dummy : public Constraint
{
private:
    IntegerVariableID var;

public:
    Dummy(const IntegerVariableID v1) :
        var(v1)
    {
    }

    auto describe_for_proof() -> std::string
    {
        return "dummy";
    }

    virtual auto install(Propagators & propagators, State & state) && -> void override
    {
        propagators.install([var = var](State & state) -> pair<Inference, PropagatorState> {
            state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                proof.emit_proof_line("p 1 s", ProofLevel::Temporary);
                proof.emit_proof_line("p -1 s", ProofLevel::Temporary);
                state.infer_true(JustifyExplicitly{[&](Proof & proof) {
                    proof.emit_proof_comment("Is this what's breaking it?");
                }});
                proof.emit_proof_line("p -1 s", ProofLevel::Temporary);
                proof.emit_rup_proof_line_under_trail(state, WeightedPseudoBooleanSum{} + 1_i * var >= 0_i, ProofLevel::Current);
            }});
            return pair{Inference::NoChange, PropagatorState::Enable};
        },
            Triggers{}, "dummy");
    }

    auto clone() const -> unique_ptr<Constraint>
    {
        return make_unique<Dummy>(var);
    }
};

auto main(int argc, char * argv[]) -> int
{
    Problem p;
    auto x = p.create_integer_variable(1_i, 3_i);
    p.post(Dummy{x});
    solve(p, SolutionCallback{}, make_optional<ProofOptions>("break_temporary.opb", "break_temporary.veripb"));
    return EXIT_SUCCESS;
}
