import ResolutionOrbitCompressionMaster
import ResolutionPointIsolationCompletion

/-!
# Compression plus point isolation

Research branch simplification of the compression--escape architecture.
Trajectory compression already provides the Cauchy half. Point isolation shows
that a Cauchy sequence can converge to a generated Answer only by becoming
eventually literally constant. Therefore no candidate-tailored escape
construction is needed once non-eventual constancy of the sampled orbit is
known.
-/

universe u v

namespace Resolution
namespace OrbitCompression

open Resolution.External
open Resolution.External.FinitePatternRealization
open Resolution.Orbit

variable {Sigma : Signature.{u}}

/-- Exact minimal anti-limit hypothesis for a compressed orbit: its factorial
sample does not eventually become a single generated Answer. -/
def FactorialSampleNontrivial
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D) : Prop :=
  ¬ EventuallyConstant D (factorialSample W)

/-- Compression plus non-eventual constancy forces incompleteness. Relative
point isolation supplies the no-generated-limit conclusion automatically. -/
theorem notComplete_of_compression_and_nontriviality
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hne : FactorialSampleNontrivial W) :
    ¬ Filtered.Complete (generatedFilteredSpace D) := by
  exact
    (generatedNotComplete_iff_exists_cauchy_not_eventuallyConstant D).2
      ⟨factorialSample W, factorialSample_cauchy W, hne⟩

/-- Simplified properness theorem: trajectory compression plus a
non-eventually-constant factorial sample makes the completion embedding
non-surjective. -/
theorem embeddingNotSurjective_of_compression_and_nontriviality
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hne : FactorialSampleNontrivial W) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  cauchy_not_eventuallyConstant_implies_completionEmbed_not_surjective
    D (factorialSample W) (factorialSample_cauchy W) hne

/-- Injectivity of the sampled family is a simple sufficient condition for
non-eventual constancy. -/
theorem factorialSampleNontrivial_of_injective
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hinj : Function.Injective (factorialSample W)) :
    FactorialSampleNontrivial W := by
  rintro ⟨x, N, hN⟩
  have hEq : factorialSample W N = factorialSample W (N + 1) := by
    calc
      factorialSample W N = x := hN N (Nat.le_refl N)
      _ = factorialSample W (N + 1) :=
        (hN (N + 1) (Nat.le_succ N)).symm
  have hIndex : N = N + 1 := hinj hEq
  omega

/-- Stronger and easier-to-use criterion: injectivity of the underlying
syntactic orbit already implies non-eventual constancy of its factorial sample.
The only exceptional factorial collision is `0! = 1!`, so the proof compares
adjacent sample indices after stage one. -/
theorem factorialSampleNontrivial_of_term_injective
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hinj : Function.Injective W.term) :
    FactorialSampleNontrivial W := by
  rintro ⟨x, N, hN⟩
  let k := Nat.max N 1
  have hkN : N ≤ k := Nat.le_max_left N 1
  have hk1 : 1 ≤ k := Nat.le_max_right N 1
  have hEq : factorialSample W k = factorialSample W (k + 1) := by
    calc
      factorialSample W k = x := hN k hkN
      _ = factorialSample W (k + 1) :=
        (hN (k + 1) (by omega)).symm
  have hFact : fact k = fact (k + 1) := by
    apply hinj
    exact hEq
  have hPos : 0 < fact k := fact_pos k
  change fact k = (k + 1) * fact k at hFact
  omega

/-- Consequently, an injective factorial sample plus trajectory compression is
enough for properness. -/
theorem embeddingNotSurjective_of_compression_and_injectiveSample
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hinj : Function.Injective (factorialSample W)) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  embeddingNotSurjective_of_compression_and_nontriviality W
    (factorialSampleNontrivial_of_injective W hinj)

/-- More structural properness criterion: trajectory compression plus
injectivity of the original generated orbit is sufficient. No candidate-wise
anti-limit observer is needed. -/
theorem embeddingNotSurjective_of_compression_and_injectiveTerm
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hinj : Function.Injective W.term) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  embeddingNotSurjective_of_compression_and_nontriviality W
    (factorialSampleNontrivial_of_term_injective W hinj)

/-! ## Direct instances without finite-pattern escape -/

/-- Under an undefined base application, the comb family is injective because
its constructor count is `2*k+1`. -/
theorem finiteBaseCompression_term_injective
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a z : D.Carrier)
    {baseSize : Nat}
    (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    Function.Injective (finiteBaseCompression D f a z C hUndefined).term := by
  intro i j hij
  change Resolution.Probe.comb D f a z i =
    Resolution.Probe.comb D f a z j at hij
  have hraw := congrArg Subtype.val hij
  have hcount := congrArg
    (Resolution.External.FiniteTagProof.nodeCount D) hraw
  rw [Resolution.Probe.combRaw_nodeCount D f a z hUndefined i,
    Resolution.Probe.combRaw_nodeCount D f a z hUndefined j] at hcount
  omega

/-- Finite-base properness now factors through compression plus syntactic
injectivity alone. The candidate-tailored anti-limit construction is not needed
for this implication. -/
theorem finiteBase_embeddingNotSurjective_via_pointIsolation
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a z : D.Carrier)
    {baseSize : Nat}
    (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  embeddingNotSurjective_of_compression_and_injectiveTerm
    (finiteBaseCompression D f a z C hUndefined)
    (finiteBaseCompression_term_injective D f a z C hUndefined)

/-- Old-fixing properness has the same shorter proof: the existing
`iterateAnswer_injective` theorem supplies all anti-limit information once point
isolation is available. -/
theorem oldFixing_embeddingNotSurjective_via_pointIsolation
    (D : PartialAlg.{u,v} Sigma)
    (W : OldFixingContextWitness D) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  embeddingNotSurjective_of_compression_and_injectiveTerm
    (oldFixingCompression D W)
    (Resolution.OldFixingContextProperness.iterateAnswer_injective D W)

end OrbitCompression
end Resolution
