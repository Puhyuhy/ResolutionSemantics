import ResolutionSemantics
import ResolutionOnePointCompletion

namespace ResolutionSemantics
namespace OnePointCompletion

abbrev Completion :=
  Resolution.Filtered.Completion
    (Resolution.External.generatedFilteredSpace Resolution.OnePoint.alg)

/-- The canonical embedding is not surjective in the one-point example. -/
theorem embeddingNotSurjective :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace Resolution.OnePoint.alg)) :=
  Resolution.OnePoint.completionEmbedding_not_surjective

/-- The completion contains a point outside the generated finite-Answer image. -/
theorem addsPoint :
    ∃ q : Completion,
      ∀ x : Resolution.Free.GeneratedAns Resolution.OnePoint.alg,
        Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace Resolution.OnePoint.alg) x
          ≠ q :=
  Resolution.OnePoint.completion_adds_point

end OnePointCompletion
end ResolutionSemantics
