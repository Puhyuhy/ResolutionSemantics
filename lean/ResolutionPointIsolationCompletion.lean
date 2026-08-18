import ResolutionPointIsolation

/-!
# Completion consequences of point isolation

Research branch probe.  Once every generated Answer is isolated by one finite
observation stage, convergence to a generated Answer is exactly eventual
constancy.  Hence the generated Resolution space is incomplete exactly when it
admits a Cauchy sequence that is not eventually constant.
-/

universe u v

namespace Resolution
namespace External
namespace FinitePatternRealization

variable {Sigma : Signature.{u}}
variable (D : PartialAlg.{u,v} Sigma)

/-- A sequence is eventually constant at the specified generated Answer. -/
def EventuallyConstantAt
    (s : Nat -> Free.GeneratedAns D)
    (x : Free.GeneratedAns D) : Prop :=
  Exists fun N : Nat => forall k : Nat, N <= k -> s k = x

/-- A sequence is eventually constant at some generated Answer. -/
def EventuallyConstant
    (s : Nat -> Free.GeneratedAns D) : Prop :=
  Exists fun x : Free.GeneratedAns D => EventuallyConstantAt D s x

/-- Point isolation in the observational filtration: each generated Answer has
    a finite stage whose equivalence class is a singleton. -/
theorem finiteTagEqAt_singleton
    (x : Free.GeneratedAns D) :
    Exists fun n : Nat => forall y : Free.GeneratedAns D,
      FiniteTagEqAt D n x y <-> y = x := by
  rcases generatedPointIsolated D x with ⟨n, T, hT⟩
  refine ⟨n, ?_⟩
  intro y
  constructor
  · intro hxy
    exact (hT y).1 (hxy T).symm
  · intro hy
    cases hy
    exact finiteTagEqAt_refl D n x

/-- Convergence to a generated Answer is rigid: it is equivalent to eventual
    literal equality with that Answer. -/
theorem filteredConverges_iff_eventuallyConstantAt
    (s : Nat -> Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    Filtered.Converges (generatedFilteredSpace D) s x <->
      EventuallyConstantAt D s x := by
  constructor
  · intro hconv
    rcases finiteTagEqAt_singleton D x with ⟨n, hisolated⟩
    rcases hconv n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    have heq : FiniteTagEqAt D n x (s k) := hN k hk
    exact (hisolated (s k)).1 heq
  · rintro ⟨N, hN⟩
    intro n
    refine ⟨N, ?_⟩
    intro k hk
    have hkx : s k = x := hN k hk
    rw [hkx]
    exact (generatedFilteredSpace D).eqAt_refl n x

/-- Completeness of generated Answers is exactly the assertion that every
    Cauchy sequence eventually becomes literally constant. -/
theorem generatedComplete_iff_allCauchyEventuallyConstant :
    Filtered.Complete (generatedFilteredSpace D) <->
      forall s : Nat -> Free.GeneratedAns D,
        Filtered.Cauchy (generatedFilteredSpace D) s ->
          EventuallyConstant D s := by
  constructor
  · intro hcomplete s hs
    rcases hcomplete s hs with ⟨x, hx⟩
    exact ⟨x, (filteredConverges_iff_eventuallyConstantAt D s x).1 hx⟩
  · intro hall s hs
    rcases hall s hs with ⟨x, hx⟩
    exact ⟨x, (filteredConverges_iff_eventuallyConstantAt D s x).2 hx⟩

/-- The generated observational space is incomplete exactly when there exists
    a Cauchy sequence that is not eventually constant. -/
theorem generatedNotComplete_iff_exists_cauchy_not_eventuallyConstant :
    (not Filtered.Complete (generatedFilteredSpace D)) <->
      Exists fun s : Nat -> Free.GeneratedAns D =>
        Filtered.Cauchy (generatedFilteredSpace D) s /\
          not EventuallyConstant D s := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    apply hnot
    apply (generatedComplete_iff_allCauchyEventuallyConstant D).2
    intro s hs
    by_contra hne
    apply hnone
    exact ⟨s, hs, hne⟩
  · rintro ⟨s, hs, hne⟩ hcomplete
    have hall := (generatedComplete_iff_allCauchyEventuallyConstant D).1 hcomplete
    exact hne (hall s hs)

/-- Properness of the generic filtered completion has the same exact criterion:
    a non-eventually-constant Cauchy sequence exists in generated Answers. -/
theorem completionEmbed_not_surjective_iff_exists_cauchy_not_eventuallyConstant :
    (not Function.Surjective
      (Filtered.embed (generatedFilteredSpace D))) <->
      Exists fun s : Nat -> Free.GeneratedAns D =>
        Filtered.Cauchy (generatedFilteredSpace D) s /\
          not EventuallyConstant D s := by
  constructor
  · intro hnotSurj
    apply (generatedNotComplete_iff_exists_cauchy_not_eventuallyConstant D).1
    intro hcomplete
    exact hnotSurj
      ((Filtered.complete_iff_embed_surjective
        (generatedFilteredSpace D)).1 hcomplete)
  · intro hex hsurj
    have hcomplete : Filtered.Complete (generatedFilteredSpace D) :=
      (Filtered.complete_iff_embed_surjective
        (generatedFilteredSpace D)).2 hsurj
    exact (generatedNotComplete_iff_exists_cauchy_not_eventuallyConstant D).2
      hex hcomplete

/-- Convenient one-way master form: any Cauchy sequence that is not eventually
    constant forces the Resolution completion embedding to be non-surjective. -/
theorem cauchy_not_eventuallyConstant_implies_completionEmbed_not_surjective
    (s : Nat -> Free.GeneratedAns D)
    (hs : Filtered.Cauchy (generatedFilteredSpace D) s)
    (hne : not EventuallyConstant D s) :
    not Function.Surjective
      (Filtered.embed (generatedFilteredSpace D)) :=
  (completionEmbed_not_surjective_iff_exists_cauchy_not_eventuallyConstant D).2
    ⟨s, hs, hne⟩

end FinitePatternRealization
end External
end Resolution
