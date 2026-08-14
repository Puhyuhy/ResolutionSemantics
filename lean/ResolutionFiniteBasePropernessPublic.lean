import ResolutionFiniteBaseProperness

/-! Public Paper I interface for the finite-base properness criterion. -/

universe u v

namespace ResolutionSemantics
namespace FiniteBaseCompletion

variable {Sigma : Resolution.Signature.{u}}

/-- Totality of the old partial evaluator. -/
abbrev IsTotal (D : Resolution.PartialAlg.{u,v} Sigma) : Prop :=
  Resolution.FiniteBaseProperness.IsTotal D

/-- For a finitely coded base, the generated observational space is complete
    exactly when the old evaluator is total. -/
theorem completeIffTotal
    (D : Resolution.PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Resolution.Orbit.Coded D.Carrier baseSize) :
    Resolution.Filtered.Complete
        (Resolution.External.generatedFilteredSpace D) ↔
      IsTotal D :=
  Resolution.FiniteBaseProperness.complete_iff_total D C

/-- The completion embedding is surjective exactly in the total case. -/
theorem embeddingSurjectiveIffTotal
    (D : Resolution.PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Resolution.Orbit.Coded D.Carrier baseSize) :
    Function.Surjective
        (Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace D)) ↔
      IsTotal D :=
  Resolution.FiniteBaseProperness.completionEmbedding_surjective_iff_total D C

/-- The completion is proper exactly when some old application is undefined. -/
theorem embeddingNotSurjectiveIffExistsUndefined
    (D : Resolution.PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Resolution.Orbit.Coded D.Carrier baseSize) :
    (¬ Function.Surjective
        (Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace D))) ↔
      exists f : Sigma.Op, exists a b : D.Carrier,
        D.eval f a b = none :=
  Resolution.FiniteBaseProperness.completionEmbedding_not_surjective_iff_exists_undefined
    D C

end FiniteBaseCompletion
end ResolutionSemantics
