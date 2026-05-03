#include <gcs/constraints/innards/recover_am1.hh>
#include <gcs/exception.hh>

#include <util/enumerate.hh>

#include <sstream>

using namespace gcs;
using namespace gcs::innards;

using std::function;
using std::stringstream;
using std::vector;

template <typename Literal_>
[[nodiscard]] auto gcs::innards::recover_am1(
    ProofLogger & logger,
    ProofLevel level,
    const vector<Literal_> & atoms,
    const function<auto(const Literal_ &, const Literal_ &)->ProofLine> & pair_ne) -> ProofLine
{
    if (atoms.size() < 2)
        throw UnexpectedException{"recover_am1 requires at least 2 atoms"};

    auto temporary_proof_level = logger.temporary_proof_level();

    stringstream am1;
    for (unsigned i1 = 1; i1 < atoms.size(); ++i1) {
        vector<ProofLine> lines;
        for (unsigned i2 = 0; i2 < i1; ++i2)
            lines.push_back(pair_ne(atoms[i1], atoms[i2]));

        if (i1 == 1)
            am1 << "pol";
        else
            am1 << " " << (i1 + 1) << " *";

        for (const auto & [n, line] : enumerate(lines)) {
            am1 << " " << line;
            if (n != 0 || i1 != 1)
                am1 << " +";
        }

        am1 << " " << (i1 + 2) << " d";
    }
    am1 << ';';
    auto result = logger.emit_proof_line(am1.str(), level);
    logger.forget_proof_level(temporary_proof_level);
    return result;
}

template auto gcs::innards::recover_am1<IntegerVariableCondition>(
    ProofLogger &, ProofLevel, const vector<IntegerVariableCondition> &, const function<auto(const IntegerVariableCondition &, const IntegerVariableCondition &)->ProofLine> &) -> ProofLine;
