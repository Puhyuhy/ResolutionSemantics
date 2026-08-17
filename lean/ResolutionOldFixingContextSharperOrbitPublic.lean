import ResolutionOldFixingContextSharperOrbit
import ResolutionOldFixingContextPropernessPublic

/-! Public research-branch interface for the sharper old-fixing orbit bound. -/

universe u v

namespace ResolutionSemantics
namespace OldFixingContextCompletion

variable {Sigma : Resolution.Signature.{u}}

/-- At stage `n`, the old-fixing orbit already identifies the consecutive
factorial iterates `(n+1)!` and `(n+2)!`. This improves the original public
witness pair `(n+2)!`, `(n+3)!`. -/
theorem sharperFactorialPairEqAt
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) (n : Nat) :
    Resolution.External.FiniteTagEqAt D n
      (factorialSequence D W (n + 1))
      (factorialSequence D W (n + 2)) :=
  Resolution.OldFixingContextProperness.sharper_factorial_pair_eqAt D W

/-- The sharper consecutive factorial pair is genuinely distinct. -/
theorem sharperFactorialPairNe
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) (n : Nat) :
    factorialSequence D W (n + 1) ≠ factorialSequence D W (n + 2) := by
  intro h
  have hindex :
      Resolution.Orbit.fact (n + 1) = Resolution.Orbit.fact (n + 2) :=
    Resolution.OldFixingContextProperness.iterateAnswer_injective D W h
  have hstrict :
      Resolution.Orbit.fact (n + 1) < Resolution.Orbit.fact (n + 2) := by
    exact Resolution.OldFixingContextProperness.fact_succ_strict (by omega)
  omega

/-- Consequently the least finite-complement separation budget of the sharper
pair is strictly greater than `n`. -/
theorem sharperSeparationRankGreaterThanBudget
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) (n : Nat) :
    n < Resolution.External.finiteSeparationRank D
      (factorialSequence D W (n + 1))
      (factorialSequence D W (n + 2)) := by
  apply (Resolution.External.finiteTagEqAt_iff_lt_rank D
    (sharperFactorialPairNe D W n) n).1
  exact sharperFactorialPairEqAt D W n

end OldFixingContextCompletion
end ResolutionSemantics
