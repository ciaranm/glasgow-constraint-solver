#include <gcs/constraint.hh>
#include <gcs/exception.hh>

#include <typeinfo>

using std::string;

using namespace gcs;

Constraint::~Constraint() = default;

auto Constraint::s_exprify(const innards::ProofModel * const) const -> string
{
    throw UnimplementedException{"No s_exprify implementation for constraint type " + string{typeid(*this).name()}};
}
