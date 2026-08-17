import ResolutionIntrinsicFiniteComplementAPI
import ResolutionFiniteBasePropernessPublic
import ResolutionOldFixingContextPropernessPublic
import ResolutionOldFixingContextSharperOrbitPublic
import ResolutionFinitePatternRealizationPublic
import ResolutionOrbitCompressionMaster
import ResolutionFinitePatternAntiLimit

/-!
# Master theorem facade for relative separation and proper completion

The checked architecture now has two independent structural ingredients:

1. relative finite-pattern realization over the pointwise-fixed partial base;
2. finite trajectory compression for the relevant observer orbit.

For growing unary syntax, the concrete finite-pattern construction supplies an
anti-limit principle: retain the candidate and a finite orbit prefix exactly,
then force the first unseen continuation into absorbing overflow. Combining
this escape mechanism with trajectory compression yields a proper completion.

The factorial-periodicity/Cauchy half is standard finite-dynamics machinery.
The Resolution-specific content lies in the relative observer class and in the
finite-pattern escape mechanism that rules out every finite generated limit.
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

/-- The finite-base criterion: the completion embedding is proper exactly when
some base application is undefined. -/
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

/-- A growing unary orbit has the syntactic escape shape needed by the generic
finite-pattern anti-limit construction. -/
abbrev EscapingUnarySyntax
    {D : Resolution.PartialAlg.{u,v} Sigma}
    (W : OrbitCompressionWitness D) :=
  Resolution.FinitePatternAntiLimit.EscapingUnarySyntax W

/-- Resolution-specific anti-limit half: finite-pattern realization plus
syntactic escape rules out convergence of the factorial sample to every
generated Answer. -/
theorem finitePatternEscapeNoGeneratedLimit
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OrbitCompressionWitness D)
    (U : EscapingUnarySyntax W) :
    Resolution.OrbitCompression.NoGeneratedLimit W :=
  Resolution.FinitePatternAntiLimit.noGeneratedLimit_of_escapingSyntax D W U

/-- Combined master properness theorem. Uniform finite trajectory compression
supplies Cauchy behavior, while finite-pattern escape supplies the absence of a
generated limit. Therefore the generated observational space is incomplete. -/
theorem compressedEscapingOrbitNotComplete
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OrbitCompressionWitness D)
    (U : EscapingUnarySyntax W) :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D) :=
  Resolution.FinitePatternAntiLimit.notComplete_of_compressed_escapingSyntax
    D W U

/-- Publication-facing proper-completion form of the combined master theorem. -/
theorem compressedEscapingOrbitEmbeddingNotSurjective
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : OrbitCompressionWitness D)
    (U : EscapingUnarySyntax W) :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace D)) :=
  Resolution.FinitePatternAntiLimit.embeddingNotSurjective_of_compressed_escapingSyntax
    D W U

/-- More general abstract Master-II implication when no-generated-limit is
provided by some other mechanism. -/
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

/-- The old-fixing infinite-base theorem factors through abstract trajectory
compression. -/
theorem oldFixingPropernessViaAbstractCompression
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : Resolution.OldFixingContextWitness D) :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D) :=
  Resolution.OrbitCompression.oldFixing_notComplete_via_compression D W

/-- The same old-fixing theorem also factors through the combined
compression-plus-finite-pattern-escape master theorem. -/
theorem oldFixingPropernessViaCombinedMaster
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (W : Resolution.OldFixingContextWitness D) :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D) :=
  Resolution.FinitePatternAntiLimit.oldFixing_notComplete_via_master D W

/-- Consequences supplied by finite orbit compression in the concrete
old/base-fixing unary context. -/
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

/-- Old-fixing concrete package, retained as a manuscript-facing instance. -/
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
