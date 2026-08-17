import ResolutionIntrinsicFiniteComplementAPI
import ResolutionFiniteBasePropernessPublic
import ResolutionOldFixingContextPropernessPublic
import ResolutionOldFixingContextSharperOrbitPublic
import ResolutionFinitePatternRealizationPublic

/-!
# Master theorem facade for relative separation and orbit compression

This module reorganizes the checked public results around two structural
principles isolated by the post-audit reduction:

1. finite-pattern realization over the pointwise-fixed partial base;
2. finite orbit compression, whose old-fixing instance yields a Cauchy orbit
   with no generated limit and hence a proper completion.

Finite-pattern realization strengthens pairwise separation: one compatible
finite-tag observer is simultaneously injective on any chosen finite list of
generated Answers. Pairwise separation is the two-point instance.

The old-fixing branch also uses the sharper observation that a stage-`n`
orbit either enters the fixed base and stabilizes or remains in only `n+1`
outside states. Consequently the consecutive factorial pair `(n+1)!`,
`(n+2)!` already agrees at stage `n`.
-/

universe u v

namespace ResolutionSemantics
namespace MasterTheorems

variable {Sigma : Resolution.Signature.{u}}

/-- Master I: one compatible finite-complement observer is injective on every
chosen finite pattern of generated Answers. -/
theorem relativeFinitePatternRealization
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (xs : List (Resolution.Free.GeneratedAns D)) :
    ∃ n : Nat, ∃ T : Resolution.External.FiniteTagAlg D n,
      ∀ {x y : Resolution.Free.GeneratedAns D}, x ∈ xs -> y ∈ xs ->
        Resolution.Free.TotalAlg.interp D (T.toTotalAlg D) x =
          Resolution.Free.TotalAlg.interp D (T.toTotalAlg D) y -> x = y :=
  FinitePattern.realization D xs

/-- The intrinsic pairwise separation theorem is retained as the observer-class
form of the two-point consequence. -/
theorem relativeFiniteComplementSeparation
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Resolution.External.IntrinsicFiniteComplementSeparating D :=
  qualitativeFiniteComplementSeparating_theorem D

/-- The finite-base criterion packaged as a consequence of bounded observer
state spaces: the completion embedding is proper exactly when some base
application is undefined. -/
theorem finiteBasePropernessCriterion
    (D : Resolution.PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Resolution.Orbit.Coded D.Carrier baseSize) :
    (¬ Function.Surjective
        (Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace D))) ↔
      exists f : Sigma.Op, exists a b : D.Carrier,
        D.eval f a b = none :=
  FiniteBaseCompletion.embeddingNotSurjectiveIffExistsUndefined D C

/-- Consequences supplied by finite orbit compression in the presence of an
old/base-fixing unary context. Keeping this as one record makes explicit that
the Cauchy witness, failure of generated convergence, incompleteness, and
properness are one package rather than independent mechanisms. -/
structure OrbitCompressionConsequences
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OldFixingContextCompletion.Witness D) : Prop where
  cauchy :
    Resolution.Filtered.Cauchy
      (Resolution.External.generatedFilteredSpace D)
      (OldFixingContextCompletion.factorialSequence D W)
  noGeneratedLimit :
    forall x : Resolution.Free.GeneratedAns D,
      ¬ Resolution.Filtered.Converges
        (Resolution.External.generatedFilteredSpace D)
        (OldFixingContextCompletion.factorialSequence D W) x
  notComplete :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D)
  embeddingNotSurjective :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace D))

/-- Master II, old-fixing instance: one witness yields the full
proper-completion package. -/
theorem oldFixingOrbitCompression
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OldFixingContextCompletion.Witness D) :
    OrbitCompressionConsequences D W := by
  refine {
    cauchy := OldFixingContextCompletion.factorialSequenceCauchy D W
    noGeneratedLimit := ?_
    notComplete := OldFixingContextCompletion.notComplete D W
    embeddingNotSurjective :=
      OldFixingContextCompletion.embeddingNotSurjective D W
  }
  intro x
  exact OldFixingContextCompletion.factorialSequenceNoLimit D W x

/-- Sharper unbounded-rank witness: at stage `n`, the distinct consecutive
factorial iterates `(n+1)!` and `(n+2)!` still agree. -/
theorem oldFixingRanksUnbounded
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OldFixingContextCompletion.Witness D) (n : Nat) :
    n < Resolution.External.finiteSeparationRank D
      (OldFixingContextCompletion.factorialSequence D W (n + 1))
      (OldFixingContextCompletion.factorialSequence D W (n + 2)) :=
  OldFixingContextCompletion.sharperSeparationRankGreaterThanBudget D W n

end MasterTheorems
end ResolutionSemantics
