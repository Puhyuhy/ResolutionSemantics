import ResolutionIntrinsicFiniteComplementAPI
import ResolutionFiniteBasePropernessPublic
import ResolutionOldFixingContextPropernessPublic
import ResolutionOldFixingContextSharperOrbitPublic
import ResolutionFinitePatternRealizationPublic
import ResolutionOrbitCompressionMaster

/-!
# Master theorem facade for relative separation and orbit compression

This module reorganizes the checked public results around two structural
principles isolated by the post-audit reduction:

1. finite-pattern realization over the pointwise-fixed partial base;
2. trajectory-level finite orbit compression plus a Resolution-specific
   no-generated-limit witness, yielding a proper completion.

Finite-pattern realization strengthens pairwise separation: one compatible
finite-tag observer is simultaneously injective on any chosen finite list of
generated Answers. Pairwise separation is the two-point instance.

Master II is deliberately split. The factorial-periodicity/Cauchy half is the
standard finite-dynamics mechanism and only requires a finite code of the
relevant observer trajectory, not a finite observer carrier. The no-limit half
remains Resolution-specific and is supplied by selected finite patterns plus
absorbing overflow.

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

/-- Abstract Master-II witness: a generated unary family whose interpretation
in every stage observer is one deterministic trajectory admitting a uniformly
bounded finite trajectory code. The ambient observer carrier may be infinite. -/
abbrev OrbitCompressionWitness
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.OrbitCompression.ObserverOrbitCompression D

/-- The factorial sample associated with an abstract compressed orbit. -/
abbrev orbitCompressionFactorialSample
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (W : OrbitCompressionWitness D) :=
  Resolution.OrbitCompression.factorialSample W

/-- Standard dynamic half of Master II: finite trajectory compression at every
stage forces the factorial sample to be Cauchy. -/
theorem orbitCompressionCauchy
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OrbitCompressionWitness D) :
    Resolution.Filtered.Cauchy
      (Resolution.External.generatedFilteredSpace D)
      (orbitCompressionFactorialSample W) :=
  Resolution.OrbitCompression.factorialSample_cauchy W

/-- Master II in abstract form. If the compressed factorial orbit additionally
has no generated limit, then the generated filtered space is incomplete. -/
theorem orbitCompressionNotComplete
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OrbitCompressionWitness D)
    (hNo : Resolution.OrbitCompression.NoGeneratedLimit W) :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D) :=
  Resolution.OrbitCompression.notComplete_of_compression W hNo

/-- Equivalent proper-completion conclusion of abstract Master II. -/
theorem orbitCompressionEmbeddingNotSurjective
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OrbitCompressionWitness D)
    (hNo : Resolution.OrbitCompression.NoGeneratedLimit W) :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace D)) :=
  Resolution.OrbitCompression.embeddingNotSurjective_of_compression W hNo

/-- Both the finite-base undefined-comb theorem and the infinite-base
old-fixing theorem instantiate the same abstract trajectory-compression
principle. -/
theorem oldFixingPropernessViaAbstractCompression
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : Resolution.OldFixingContextWitness D) :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D) :=
  Resolution.OrbitCompression.oldFixing_notComplete_via_compression D W

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

/-- Old-fixing concrete package, retained as the manuscript-facing instance of
abstract Master II. -/
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
