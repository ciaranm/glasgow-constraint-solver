#include <gcs/innards/inference_tracker.hh>

#include <tuple>

using std::optional;
using std::tuple;
using std::vector;

using namespace gcs;
using namespace gcs::innards;

struct LazyProofGenerationInferenceTracker::Imp
{
    vector<tuple<Literal, Justification, Reason>> pending_proof_steps;
    optional<Reason> failing_reason;
};

LazyProofGenerationInferenceTracker::LazyProofGenerationInferenceTracker(State & s, ProofLogger & l) :
    _imp(new Imp()),
    state(s),
    logger(l)
{
}

auto LazyProofGenerationInferenceTracker::track(const Literal & lit, HowChanged how, const Justification & why,
    const Reason & reason) -> void
{
    switch (how) {
    case HowChanged::Unchanged:
        break;
    case HowChanged::BoundsChanged:
    case HowChanged::InteriorValuesChanged:
    case HowChanged::Instantiated:
        changes.emplace_back(lit, how);
        _imp->pending_proof_steps.emplace_back(lit, why, reason);
        break;
    [[unlikely]] case HowChanged::Contradiction:
        _imp->pending_proof_steps.emplace_back(lit, why, reason);
        _imp->failing_reason = reason;
        throw TrackedPropagationFailed{};
    }
}

auto LazyProofGenerationInferenceTracker::for_each_pending_proof_step(const std::function<auto(const Literal &, const Justification &, const Reason &)->void> & f) -> void
{
    for (const auto & [lit, just, reason] : _imp->pending_proof_steps)
        f(lit, just, reason);
    _imp->pending_proof_steps.clear();
}

LazyProofGenerationInferenceTracker::~LazyProofGenerationInferenceTracker() = default;
