import ResolutionPointIsolation

/-!
# Completion consequences of point isolation

The convergence-rigidity argument is entirely generic once a filtered space has
point-isolating finite stages.  Resolution Semantics enters only by proving that
its generated filtered space has this property via singleton finite-pattern
observers.
-/

universe u v

namespace Resolution

namespace Filtered

/-- A separated filtered space is point-isolated when every point has some
finite stage whose equivalence class is exactly that singleton. -/
def PointIsolated (S : Space.{u}) : Prop :=
  ∀ x : S.Carrier, ∃ n : Nat, ∀ y : S.Carrier,
    S.eqAt n x y ↔ y = x

/-- Eventual literal constancy at a specified point. -/
def EventuallyConstantAt
    {S : Space.{u}}
    (s : Nat → S.Carrier)
    (x : S.Carrier) : Prop :=
  ∃ N : Nat, ∀ k : Nat, N ≤ k → s k = x

/-- Eventual literal constancy at some point. -/
def EventuallyConstant
    {S : Space.{u}}
    (s : Nat → S.Carrier) : Prop :=
  ∃ x : S.Carrier, EventuallyConstantAt s x

/-- In a point-isolated filtered space, convergence to a point is exactly
literal eventual constancy at that point. -/
theorem converges_iff_eventuallyConstantAt_of_pointIsolated
    (S : Space.{u})
    (hIso : PointIsolated S)
    (s : Nat → S.Carrier)
    (x : S.Carrier) :
    Converges S s x ↔ EventuallyConstantAt s x := by
  constructor
  · intro hconv
    rcases hIso x with ⟨n, hisolated⟩
    rcases hconv n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (hisolated (s k)).1 (hN k hk)
  · rintro ⟨N, hN⟩
    intro n
    refine ⟨N, ?_⟩
    intro k hk
    rw [hN k hk]
    exact S.eqAt_refl n x

/-- For a point-isolated filtered space, completeness says precisely that every
Cauchy sequence eventually becomes literally constant. -/
theorem complete_iff_allCauchyEventuallyConstant_of_pointIsolated
    (S : Space.{u})
    (hIso : PointIsolated S) :
    Complete S ↔
      ∀ s : Nat → S.Carrier, Cauchy S s → EventuallyConstant s := by
  constructor
  · intro hcomplete s hs
    rcases hcomplete s hs with ⟨x, hx⟩
    exact ⟨x,
      (converges_iff_eventuallyConstantAt_of_pointIsolated S hIso s x).1 hx⟩
  · intro hall s hs
    rcases hall s hs with ⟨x, hx⟩
    exact ⟨x,
      (converges_iff_eventuallyConstantAt_of_pointIsolated S hIso s x).2 hx⟩

/-- In a point-isolated filtered space, incompleteness is equivalent to the
existence of a Cauchy sequence that never becomes eventually constant. -/
theorem notComplete_iff_exists_cauchy_not_eventuallyConstant_of_pointIsolated
    (S : Space.{u})
    (hIso : PointIsolated S) :
    (¬ Complete S) ↔
      ∃ s : Nat → S.Carrier, Cauchy S s ∧ ¬ EventuallyConstant s := by
  classical
  constructor
  · intro hnot
    apply Classical.byContradiction
    intro hnone
    apply hnot
    apply (complete_iff_allCauchyEventuallyConstant_of_pointIsolated S hIso).2
    intro s hs
    apply Classical.byContradiction
    intro hne
    apply hnone
    exact ⟨s, hs, hne⟩
  · rintro ⟨s, hs, hne⟩ hcomplete
    have hall :=
      (complete_iff_allCauchyEventuallyConstant_of_pointIsolated S hIso).1 hcomplete
    exact hne (hall s hs)

/-- Properness of the generic Cauchy completion has the same exact criterion in
a point-isolated filtered space. -/
theorem embed_not_surjective_iff_exists_cauchy_not_eventuallyConstant_of_pointIsolated
    (S : Space.{u})
    (hIso : PointIsolated S) :
    (¬ Function.Surjective (embed S)) ↔
      ∃ s : Nat → S.Carrier, Cauchy S s ∧ ¬ EventuallyConstant s := by
  rw [← complete_iff_embed_surjective S]
  exact notComplete_iff_exists_cauchy_not_eventuallyConstant_of_pointIsolated
    S hIso

/-- One-way generic properness criterion: point isolation plus a non-eventually-
constant Cauchy sequence forces the completion embedding to be non-surjective. -/
theorem cauchy_not_eventuallyConstant_implies_embed_not_surjective
    (S : Space.{u})
    (hIso : PointIsolated S)
    (s : Nat → S.Carrier)
    (hs : Cauchy S s)
    (hne : ¬ EventuallyConstant s) :
    ¬ Function.Surjective (embed S) :=
  (embed_not_surjective_iff_exists_cauchy_not_eventuallyConstant_of_pointIsolated
    S hIso).2 ⟨s, hs, hne⟩

end Filtered

namespace External
namespace FinitePatternRealization

variable {Sigma : Signature.{u}}
variable (D : PartialAlg.{u,v} Sigma)

/-- Backwards-compatible Resolution-specialized notation. -/
abbrev EventuallyConstantAt
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) : Prop :=
  Filtered.EventuallyConstantAt s x

/-- Backwards-compatible Resolution-specialized notation. -/
abbrev EventuallyConstant
    (s : Nat → Free.GeneratedAns D) : Prop :=
  Filtered.EventuallyConstant s

/-- Quantitative point isolation in the observational filtration: the canonical
stage `nodeCount x` already has singleton class at `x`. -/
theorem finiteTagEqAt_singleton_at_nodeCount
    (x : Free.GeneratedAns D) :
    ∀ y : Free.GeneratedAns D,
      FiniteTagEqAt D (nodeCount D x.1) x y ↔ y = x := by
  intro y
  constructor
  · intro hxy
    have hobs := hxy (isolationObserver D x)
    have hbudget := isolationBudget_eq_nodeCount D x
    have hrec := isolationObserver_recognizes D x y
    apply hrec.mp
    rw [hbudget] at hobs
    exact hobs.symm
  · intro hy
    cases hy
    exact finiteTagEqAt_refl D (nodeCount D x.1) x

/-- Existential form retained for compatibility with the earlier research API. -/
theorem finiteTagEqAt_singleton
    (x : Free.GeneratedAns D) :
    ∃ n : Nat, ∀ y : Free.GeneratedAns D,
      FiniteTagEqAt D n x y ↔ y = x :=
  ⟨nodeCount D x.1, finiteTagEqAt_singleton_at_nodeCount D x⟩

/-- Resolution's generated filtered space is point-isolated, with an explicit
constructor-count isolation stage for every generated Answer. -/
theorem generatedFilteredSpace_pointIsolated :
    Filtered.PointIsolated (generatedFilteredSpace D) := by
  intro x
  exact ⟨nodeCount D x.1, finiteTagEqAt_singleton_at_nodeCount D x⟩

/-- Convergence to a generated Answer is rigid: it is equivalent to eventual
literal equality with that Answer. -/
theorem filteredConverges_iff_eventuallyConstantAt
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    Filtered.Converges (generatedFilteredSpace D) s x ↔
      EventuallyConstantAt D s x :=
  Filtered.converges_iff_eventuallyConstantAt_of_pointIsolated
    (generatedFilteredSpace D) (generatedFilteredSpace_pointIsolated D) s x

/-- Completeness of generated Answers is exactly the assertion that every
Cauchy sequence eventually becomes literally constant. -/
theorem generatedComplete_iff_allCauchyEventuallyConstant :
    Filtered.Complete (generatedFilteredSpace D) ↔
      ∀ s : Nat → Free.GeneratedAns D,
        Filtered.Cauchy (generatedFilteredSpace D) s →
          EventuallyConstant D s :=
  Filtered.complete_iff_allCauchyEventuallyConstant_of_pointIsolated
    (generatedFilteredSpace D) (generatedFilteredSpace_pointIsolated D)

/-- The generated observational space is incomplete exactly when there exists
a Cauchy sequence that is not eventually constant. -/
theorem generatedNotComplete_iff_exists_cauchy_not_eventuallyConstant :
    (¬ Filtered.Complete (generatedFilteredSpace D)) ↔
      ∃ s : Nat → Free.GeneratedAns D,
        Filtered.Cauchy (generatedFilteredSpace D) s ∧
          ¬ EventuallyConstant D s :=
  Filtered.notComplete_iff_exists_cauchy_not_eventuallyConstant_of_pointIsolated
    (generatedFilteredSpace D) (generatedFilteredSpace_pointIsolated D)

/-- Properness of the generic filtered completion has the same exact criterion:
a non-eventually-constant Cauchy sequence exists in generated Answers. -/
theorem completionEmbed_not_surjective_iff_exists_cauchy_not_eventuallyConstant :
    (¬ Function.Surjective
      (Filtered.embed (generatedFilteredSpace D))) ↔
      ∃ s : Nat → Free.GeneratedAns D,
        Filtered.Cauchy (generatedFilteredSpace D) s ∧
          ¬ EventuallyConstant D s :=
  Filtered.embed_not_surjective_iff_exists_cauchy_not_eventuallyConstant_of_pointIsolated
    (generatedFilteredSpace D) (generatedFilteredSpace_pointIsolated D)

/-- Convenient one-way master form: any Cauchy sequence that is not eventually
constant forces the Resolution completion embedding to be non-surjective. -/
theorem cauchy_not_eventuallyConstant_implies_completionEmbed_not_surjective
    (s : Nat → Free.GeneratedAns D)
    (hs : Filtered.Cauchy (generatedFilteredSpace D) s)
    (hne : ¬ EventuallyConstant D s) :
    ¬ Function.Surjective
      (Filtered.embed (generatedFilteredSpace D)) :=
  Filtered.cauchy_not_eventuallyConstant_implies_embed_not_surjective
    (generatedFilteredSpace D) (generatedFilteredSpace_pointIsolated D)
    s hs hne

end FinitePatternRealization
end External
end Resolution
