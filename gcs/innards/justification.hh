#ifndef GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH
#define GLASGOW_CONSTRAINT_SOLVER_GUARD_GCS_JUSTIFICATION_HH

#include <gcs/innards/literal.hh>
#include <gcs/innards/proofs/proof_logger-fwd.hh>
#include <gcs/innards/proofs/proof_only_variables-fwd.hh>
#include <gcs/innards/reason.hh>

#ifdef GCS_TRACK_ALL_PROPAGATIONS
#include <source_location>
#endif

#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

namespace gcs::innards
{
    using RUPDependency = std::variant<
        ProofLine,
        IntegerVariableID,
        ProofOnlySimpleIntegerVariableID>;

    using RUPDependencies = std::vector<RUPDependency>;

    auto add_dependency(RUPDependencies &, const std::optional<RUPDependency> &) -> void;

    auto add_dependency(RUPDependencies &, const std::pair<std::optional<ProofLine>, std::optional<ProofLine>> &) -> void;

    /**
     * \brief Write an explicit justification to the proof. Any ProofLevel::Temporary
     * constraints will be wiped after the conclusion is derived. The reason used for
     * the outside inference is provided for convenience.
     *
     * \ingroup Innards
     * \sa JustifyExplicitly
     */
    using ExplicitJustificationFunction = std::function<auto(const Reason & reason, ProofLogger &)->void>;

    /**
     * \brief Justification for something that is actually a guess, not an
     * inferred decision.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct Guess
    {
    };

    /**
     * \brief Specify that an inference requires an explicit justification in
     * the proof log.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyExplicitly
    {
        ExplicitJustificationFunction add_proof_steps;
        std::shared_ptr<const RUPDependencies> rup_dependencies;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

        explicit JustifyExplicitly(const ExplicitJustificationFunction & a,
            const std::shared_ptr<const RUPDependencies> & d
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) :
            add_proof_steps(a),
            rup_dependencies(d)
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            where(w)
#endif
        {
        }

        explicit JustifyExplicitly(const ExplicitJustificationFunction & a
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) :
            add_proof_steps(a)
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            where(w)
#endif
        {
        }
    };

    /**
     * \brief Specify that an inference can be justified using reverse unit
     * propagation.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct JustifyUsingRUP
    {
        std::shared_ptr<const RUPDependencies> rup_dependencies;
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

        explicit JustifyUsingRUP(
            const std::shared_ptr<const RUPDependencies> & d
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            const std::source_location & w = std::source_location::current()
#endif
                ) :
            rup_dependencies(d)
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            ,
            where(w)
#endif
        {
        }

        explicit JustifyUsingRUP(
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            const std::source_location & w = std::source_location::current()
#endif
                )
#ifdef GCS_TRACK_ALL_PROPAGATIONS
            :
            where(w)
#endif
        {
        }
    };

    /**
     * \brief Specify that an inference will be asserted rather than justified.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct AssertRatherThanJustifying
    {
#ifdef GCS_TRACK_ALL_PROPAGATIONS
        std::source_location where;
#endif

#ifdef GCS_TRACK_ALL_PROPAGATIONS
        explicit AssertRatherThanJustifying(const std::source_location & w = std::source_location::current()) :
            where(w)
        {
        }
#else
        explicit AssertRatherThanJustifying()
        {
        }
#endif
    };

    /**
     * \brief Specify that an inference does not require justification.
     *
     * \ingroup Innards
     * \sa Justification
     */
    struct NoJustificationNeeded
    {
    };

    /**
     * \brief Specify why an inference is justified, for proof logging.
     *
     * \ingroup Innards
     */
    using Justification = std::variant<Guess, JustifyUsingRUP, JustifyExplicitly, AssertRatherThanJustifying, NoJustificationNeeded>;
}

#endif
