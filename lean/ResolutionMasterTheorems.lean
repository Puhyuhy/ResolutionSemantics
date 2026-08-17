import ResolutionIntrinsicFiniteComplementAPI
import ResolutionFiniteBasePropernessPublic
import ResolutionOldFixingContextPropernessPublic

/-!
# Master theorem facade for relative separation and orbit compression

This module does not introduce a new proof mechanism.  It reorganizes the
checked public results around the two structural principles isolated by the
post-audit reduction:

1. relative finite-complement separation over the pointwise-fixed partial base;
2. finite orbit compression, whose old-fixing instance yields a Cauchy orbit
   with no generated limit and hence a proper completion.

The point is to make the dependency structure explicit before attempting the
stronger finite-pattern and sharper `(n+1)!` orbit bounds on this research
branch.
-/

universe u v

namespace ResolutionSemantics
namespace MasterTheorems

variable {Sigma : Resolution.Signature.{u}}

/-- Master separation principle, currently at the pairwise strength proved in
Theorem 3.3: every unequal generated pair is separated by a compatible total
extension that fixes the base pointwise and has finite complement over it. -/
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
    (not Function.Surjective
        (Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace D))) <->
      exists f : Sigma.Op, exists a b : D.Carrier,
        D.eval f a b = none :=
  FiniteBaseCompletion.embeddingNotSurjectiveIffExistsUndefined D C

/-- Consequences supplied by finite orbit compression in the presence of an
old/base-fixing unary context.  Keeping this as one record makes explicit that
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
      not Resolution.Filtered.Converges
        (Resolution.External.generatedFilteredSpace D)
        (OldFixingContextCompletion.factorialSequence D W) x
  notComplete :
    not Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D)
  embeddingNotSurjective :
    not Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace D))

/-- Master old-fixing orbit-compression theorem: one witness yields the full
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

/-- Unbounded finite-complement separation ranks are part of the same
old-fixing orbit-compression package. -/
theorem oldFixingRanksUnbounded
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OldFixingContextCompletion.Witness D) (n : Nat) :
    n < Resolution.External.finiteSeparationRank D
      (OldFixingContextCompletion.factorialSequence D W (n + 2))
      (OldFixingContextCompletion.factorialSequence D W (n + 3)) :=
  OldFixingContextCompletion.separationRankGreaterThanBudget D W n

end MasterTheorems
end ResolutionSemantics
