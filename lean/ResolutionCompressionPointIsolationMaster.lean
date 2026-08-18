import ResolutionOrbitCompressionMaster
import ResolutionPointIsolationCompletion

/-!
# Compression plus point isolation

Research branch simplification of the compression--escape architecture.
Trajectory compression already provides the Cauchy half.  Point isolation shows
that a Cauchy sequence can converge to a generated Answer only by becoming
eventually literally constant.  Therefore no candidate-tailored escape
construction is needed once non-eventual constancy of the sampled orbit is
known.
-/

universe u v

namespace Resolution
namespace OrbitCompression

open Resolution.External
open Resolution.External.FinitePatternRealization

variable {Sigma : Signature.{u}}

/-- Exact minimal anti-limit hypothesis for a compressed orbit: its factorial
    sample does not eventually become a single generated Answer. -/
def FactorialSampleNontrivial
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D) : Prop :=
  ¬ EventuallyConstant D (factorialSample W)

/-- Compression plus non-eventual constancy forces incompleteness.  Relative
    point isolation supplies the no-generated-limit conclusion automatically. -/
theorem notComplete_of_compression_and_nontriviality
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hne : FactorialSampleNontrivial W) :
    ¬ Filtered.Complete (generatedFilteredSpace D) := by
  exact
    (generatedNotComplete_iff_exists_cauchy_not_eventuallyConstant D).2
      ⟨factorialSample W, factorialSample_cauchy W, hne⟩

/-- Simplified properness master theorem: trajectory compression plus a
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

/-- Consequently, an injective factorial sample plus trajectory compression is
    enough for properness. -/
theorem embeddingNotSurjective_of_compression_and_injectiveSample
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D)
    (hinj : Function.Injective (factorialSample W)) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  embeddingNotSurjective_of_compression_and_nontriviality W
    (factorialSampleNontrivial_of_injective W hinj)

end OrbitCompression
end Resolution
