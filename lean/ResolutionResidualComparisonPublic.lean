import ResolutionResidualComparison

/-! Public comparison API for residual finiteness and finite Rees index. -/

universe u v

namespace ResolutionSemantics
namespace ResidualComparison

variable {Sigma : Resolution.Signature.{u}}

/-- Pairwise separation by a compatible target with a finite code for its
    entire carrier. -/
abbrev FiniteCompatibleSeparatesAt
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (x y : Resolution.Free.GeneratedAns D) :=
  Resolution.ResidualComparison.FiniteCompatibleSeparatesAt D x y

/-- Ordinary residual finiteness of the generated Answer algebra. -/
abbrev GeneratedResiduallyFinite
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.ResidualComparison.GeneratedResiduallyFinite D

/-- Quantitative finite compatible separation over a finitely coded base. -/
theorem finiteBaseCompatibleSeparationBound
    (D : Resolution.PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Resolution.Orbit.Coded D.Carrier baseSize)
    (x y : Resolution.Free.GeneratedAns D) (hxy : x ≠ y) :
    Exists fun T : Resolution.Free.CompatibleAlg.{u,v,v} D =>
      Exists fun _ : Resolution.Orbit.Coded T.Carrier
          (baseSize +
            Resolution.External.FiniteTagProof.nodeCount D x.1 +
            Resolution.External.FiniteTagProof.nodeCount D y.1 + 1) =>
        Function.Injective T.embed ∧
          Resolution.Free.CompatibleAlg.interp D T x ≠
            Resolution.Free.CompatibleAlg.interp D T y :=
  Resolution.ResidualComparison.finiteBaseCompatibleSeparationBound
    D C x y hxy

/-- Generated Answers over every finitely coded old carrier are residually
    finite. -/
theorem finiteBaseGeneratedResiduallyFinite
    (D : Resolution.PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Resolution.Orbit.Coded D.Carrier baseSize) :
    GeneratedResiduallyFinite D :=
  Resolution.ResidualComparison.finiteBaseGeneratedResiduallyFinite D C

/-- Closure of the embedded old carrier under all generated total
    operations. -/
abbrev GeneratedOldClosed
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.ResidualComparison.GeneratedOldClosed D

/-- An undefined old application produces a generated Answer outside the old
    image. -/
theorem undefinedApplicationEscapesOldImage
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a b : D.Carrier)
    (hUndefined : D.eval f a b = none) :
    forall c : D.Carrier,
      Resolution.Free.generatedOp D f (Resolution.Free.generatedOld D a)
          (Resolution.Free.generatedOld D b) ≠
        Resolution.Free.generatedOld D c :=
  Resolution.ResidualComparison.undefinedApplicationEscapesOldImage
    D f a b hUndefined

/-- The old image is a total subalgebra of generated Answers exactly when the
    original evaluator is total. -/
theorem generatedOldClosedIffEvaluatorTotal
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    GeneratedOldClosed D ↔
      Resolution.FiniteBaseProperness.IsTotal D :=
  Resolution.ResidualComparison.generatedOldClosed_iff_evaluatorTotal D

end ResidualComparison
end ResolutionSemantics
