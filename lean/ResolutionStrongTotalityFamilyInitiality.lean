import ResolutionStrongTotalityFamilyNaturality

/-!
# Family initiality characterization of Strong Totality

The simultaneous universal property for a family of specifications can be
expressed intrinsically in the category of pointed family completions.  This
module proves the exact equivalence.

A universal family completion is initial: over the identity translation of the
underlying specification family, there is one and only one generator-preserving
map into every pointed family completion.  Conversely, this initiality property
recovers the full dependent extension principle by packaging an arbitrary
family of target types and interpretations as a family completion.

Together with family canonicity, this gives three equivalent descriptions of
the same object: universal dependent extension, categorical initiality, and
unique structural equivalence to the canonical Resolution family.
-/

universe u v

namespace Resolution
namespace StrongTotality

namespace FamilySpecMorphism

/-- Identity translation of a specification family. -/
def id
    {I : Type v}
    (F : I -> Specification.{u}) : FamilySpecMorphism F F where
  index := fun i => i
  mapSpec := fun i => SpecMorphism.id (F i)

end FamilySpecMorphism

/-- Family Strong Totality is exactly categorical initiality among pointed
completions of the same specification family. -/
theorem universalFamilyCompletion_iff_initial
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F) :
    IsUniversalFamilyCompletion F A ↔
      forall B : FamilyCompletionObject F,
        Exists fun p : FamilyCompletionHomOver
            (FamilySpecMorphism.id F) A B =>
          forall q : FamilyCompletionHomOver
              (FamilySpecMorphism.id F) A B,
            q = p := by
  constructor
  · intro hA B
    exact universalFamilyCompletion_relativeInitial
      (FamilySpecMorphism.id F) A B hA
  · intro hInitial
    intro Y onSolution onResidual
    let B : FamilyCompletionObject F := {
      Carrier := Y
      includeSolution := onSolution
      residual := onResidual
    }
    rcases hInitial B with ⟨p, hUnique⟩
    refine ⟨p.toFun, ?_, ?_⟩
    · constructor
      · intro i x
        have h := p.map_solution i x
        change p.toFun i (A.includeSolution i x) =
            onSolution i
              (SpecMorphism.mapSolution (SpecMorphism.id (F i)) x) at h
        rw [SpecMorphism.mapSolution_id] at h
        exact h
      · intro i
        have h := p.map_residual i
        change p.toFun i (A.residual i) = onResidual i at h
        exact h
    · intro g hg
      let q : FamilyCompletionHomOver (FamilySpecMorphism.id F) A B := {
        toFun := g
        map_solution := by
          intro i x
          change g i (A.includeSolution i x) =
            onSolution i
              (SpecMorphism.mapSolution (SpecMorphism.id (F i)) x)
          rw [SpecMorphism.mapSolution_id]
          exact hg.1 i x
        map_residual := by
          intro i
          change g i (A.residual i) = onResidual i
          exact hg.2 i
      }
      have hq : q = p := hUnique q
      funext i x
      exact congrArg (fun k => k.toFun i x) hq

/-- Categorical initiality and canonical structural classification are
equivalent descriptions of a family completion. -/
theorem familyCompletion_initial_iff_uniqueCanonicalEquiv
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F) :
    (forall B : FamilyCompletionObject F,
      Exists fun p : FamilyCompletionHomOver
          (FamilySpecMorphism.id F) A B =>
        forall q : FamilyCompletionHomOver
            (FamilySpecMorphism.id F) A B,
          q = p) ↔
      Exists fun e : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)) =>
        IsCanonicalFamilyEquiv F A e ∧
        forall g : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)),
          IsCanonicalFamilyEquiv F A g -> g = e := by
  constructor
  · intro hInitial
    have hUniversal : IsUniversalFamilyCompletion F A :=
      (universalFamilyCompletion_iff_initial F A).2 hInitial
    exact (universalFamilyCompletion_iff_uniqueCanonicalEquiv F A).1 hUniversal
  · intro hCanonical
    have hUniversal : IsUniversalFamilyCompletion F A :=
      (universalFamilyCompletion_iff_uniqueCanonicalEquiv F A).2 hCanonical
    exact (universalFamilyCompletion_iff_initial F A).1 hUniversal

end StrongTotality
end Resolution
