import ResolutionFinitePatternRealization

/-!
# Public finite-pattern realization API

Publication-facing names for the finite-pattern strengthening of pairwise
finite-complement separation.
-/

universe u v

namespace ResolutionSemantics
namespace FinitePattern

variable {Sigma : Resolution.Signature.{u}}

/-- A single compatible finite-tag observer is injective on any chosen finite
list of generated Answers. The base carrier may be infinite; only the added
state budget is finite. -/
theorem realization
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (xs : List (Resolution.Free.GeneratedAns D)) :
    ∃ n : Nat, ∃ T : Resolution.External.FiniteTagAlg D n,
      ∀ {x y : Resolution.Free.GeneratedAns D}, x ∈ xs -> y ∈ xs ->
        Resolution.Free.TotalAlg.interp D (T.toTotalAlg D) x =
          Resolution.Free.TotalAlg.interp D (T.toTotalAlg D) y -> x = y :=
  Resolution.External.FinitePatternRealization.finitePatternRealization D xs

/-- Pairwise finite-tag separation is the two-point instance of finite-pattern
realization. -/
theorem pairSeparation
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (x y : Resolution.Free.GeneratedAns D) (hxy : x ≠ y) :
    ∃ n : Nat, ∃ T : Resolution.External.FiniteTagAlg D n,
      Resolution.Free.TotalAlg.interp D (T.toTotalAlg D) x ≠
        Resolution.Free.TotalAlg.interp D (T.toTotalAlg D) y :=
  Resolution.External.FinitePatternRealization.pairSeparation_from_finitePattern
    D x y hxy

end FinitePattern
end ResolutionSemantics
