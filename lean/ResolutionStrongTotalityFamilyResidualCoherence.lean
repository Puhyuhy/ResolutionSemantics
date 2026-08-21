import ResolutionStrongTotalityFamilyResidualNaturality

/-!
# Coherence for provenance-aware family Strong Totality

The minimal family layer already has identity and composition laws forced by
its universal property.  The structured residual family layer should satisfy
the same coherence, now transporting both ordinary solutions and residual
provenance.

This module equips `ResidualFamilyCompletionHomOver` with identity and
composition, proves that all maps over a fixed structured family translation
from a universal source are equal, and derives the canonical identity and
composition laws from that uniqueness.  Hence provenance-aware transport is
coherent for the same universal reason as the minimal family semantics.
-/

universe u r v w z

namespace Resolution
namespace StrongTotality

namespace ResidualFamilyCompletionHomOver

/-- Identity map of a structured residual-family completion. -/
def id
    {I : Type v}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    (A : ResidualFamilyCompletionObject F E) :
    ResidualFamilyCompletionHomOver (FamilySemanticsMorphism.id F E) A A where
  toFun := fun _ x => x
  map_solution := by
    intro i x
    change A.includeSolution i x =
      A.includeSolution i
        (SpecMorphism.mapSolution (SpecMorphism.id (F i)) x)
    exact congrArg (A.includeSolution i)
      (SpecMorphism.mapSolution_id (F i) x).symm
  map_residual := by
    intro i q
    rfl

/-- Composition of structured family completion maps over composable semantic
family translations. -/
def comp
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    {H : K -> Specification.{u}}
    {Q : K -> Type r}
    {eta : FamilySemanticsMorphism F E G R}
    {theta : FamilySemanticsMorphism G R H Q}
    {A : ResidualFamilyCompletionObject F E}
    {B : ResidualFamilyCompletionObject G R}
    {C : ResidualFamilyCompletionObject H Q}
    (q : ResidualFamilyCompletionHomOver theta B C)
    (p : ResidualFamilyCompletionHomOver eta A B) :
    ResidualFamilyCompletionHomOver
      (FamilySemanticsMorphism.comp theta eta) A C where
  toFun := fun i x => q.toFun (eta.index i) (p.toFun i x)
  map_solution := by
    intro i x
    change q.toFun (eta.index i) (p.toFun i (A.includeSolution i x)) =
      C.includeSolution (theta.index (eta.index i))
        (SpecMorphism.mapSolution
          (SpecMorphism.comp
            (theta.specification (eta.index i))
            (eta.specification i)) x)
    calc
      q.toFun (eta.index i) (p.toFun i (A.includeSolution i x)) =
          q.toFun (eta.index i)
            (B.includeSolution (eta.index i)
              (SpecMorphism.mapSolution (eta.specification i) x)) :=
        congrArg (q.toFun (eta.index i)) (p.map_solution i x)
      _ = C.includeSolution (theta.index (eta.index i))
            (SpecMorphism.mapSolution
              (theta.specification (eta.index i))
              (SpecMorphism.mapSolution (eta.specification i) x)) :=
        q.map_solution (eta.index i)
          (SpecMorphism.mapSolution (eta.specification i) x)
      _ = C.includeSolution (theta.index (eta.index i))
            (SpecMorphism.mapSolution
              (SpecMorphism.comp
                (theta.specification (eta.index i))
                (eta.specification i)) x) :=
        congrArg (C.includeSolution (theta.index (eta.index i)))
          (SpecMorphism.mapSolution_comp
            (theta.specification (eta.index i))
            (eta.specification i) x).symm
  map_residual := by
    intro i e
    change q.toFun (eta.index i) (p.toFun i (A.includeResidual i e)) =
      C.includeResidual (theta.index (eta.index i))
        (ResidualRefinement.comp
          (theta.residual (eta.index i)) (eta.residual i) e)
    calc
      q.toFun (eta.index i) (p.toFun i (A.includeResidual i e)) =
          q.toFun (eta.index i)
            (B.includeResidual (eta.index i) (eta.residual i e)) :=
        congrArg (q.toFun (eta.index i)) (p.map_residual i e)
      _ = C.includeResidual (theta.index (eta.index i))
            (theta.residual (eta.index i) (eta.residual i e)) :=
        q.map_residual (eta.index i) (eta.residual i e)
      _ = C.includeResidual (theta.index (eta.index i))
            (ResidualRefinement.comp
              (theta.residual (eta.index i)) (eta.residual i) e) := by
        rfl

end ResidualFamilyCompletionHomOver

/-- Any two provenance-aware family maps over the same semantic translation
from a universal source are equal. -/
theorem universalResidualFamilyCompletion_homOver_subsingleton
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (A : ResidualFamilyCompletionObject F E)
    (B : ResidualFamilyCompletionObject G R)
    (hA : IsUniversalResidualFamilyCompletion F E A)
    (p q : ResidualFamilyCompletionHomOver eta A B) :
    p = q := by
  rcases universalResidualFamilyCompletion_relativeInitial eta A B hA with
    ⟨m, hUnique⟩
  exact (hUnique p).trans (hUnique q).symm

/-- Every endomorphism of a universal structured family over the identity
semantic translation is forced to be the identity map. -/
theorem universalResidualFamilyCompletion_identity_forced
    {I : Type v}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    (A : ResidualFamilyCompletionObject F E)
    (hA : IsUniversalResidualFamilyCompletion F E A)
    (p : ResidualFamilyCompletionHomOver
      (FamilySemanticsMorphism.id F E) A A) :
    p = ResidualFamilyCompletionHomOver.id A :=
  universalResidualFamilyCompletion_homOver_subsingleton
    (FamilySemanticsMorphism.id F E) A A hA p
      (ResidualFamilyCompletionHomOver.id A)

/-- Composition of provenance-aware family maps is forced by universality. -/
theorem universalResidualFamilyCompletion_composition_forced
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    {H : K -> Specification.{u}}
    {Q : K -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (theta : FamilySemanticsMorphism G R H Q)
    (A : ResidualFamilyCompletionObject F E)
    (B : ResidualFamilyCompletionObject G R)
    (C : ResidualFamilyCompletionObject H Q)
    (hA : IsUniversalResidualFamilyCompletion F E A)
    (p : ResidualFamilyCompletionHomOver eta A B)
    (q : ResidualFamilyCompletionHomOver theta B C)
    (m : ResidualFamilyCompletionHomOver
      (FamilySemanticsMorphism.comp theta eta) A C) :
    ResidualFamilyCompletionHomOver.comp q p = m :=
  universalResidualFamilyCompletion_homOver_subsingleton
    (FamilySemanticsMorphism.comp theta eta) A C hA
      (ResidualFamilyCompletionHomOver.comp q p) m

/-- Canonical provenance-aware transport over identity is the identity map. -/
theorem canonicalResidualFamilyCompletionMap_id
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r) :
    canonicalResidualFamilyCompletionMap (FamilySemanticsMorphism.id F E) =
      ResidualFamilyCompletionHomOver.id
        (canonicalResidualFamilyCompletion F E) :=
  universalResidualFamilyCompletion_identity_forced
    (canonicalResidualFamilyCompletion F E)
    (canonicalResidualFamilyCompletion_universal F E)
    (canonicalResidualFamilyCompletionMap (FamilySemanticsMorphism.id F E))

/-- Canonical provenance-aware family transport preserves composition. -/
theorem canonicalResidualFamilyCompletionMap_comp
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    {H : K -> Specification.{u}}
    {Q : K -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (theta : FamilySemanticsMorphism G R H Q) :
    ResidualFamilyCompletionHomOver.comp
        (canonicalResidualFamilyCompletionMap theta)
        (canonicalResidualFamilyCompletionMap eta) =
      canonicalResidualFamilyCompletionMap
        (FamilySemanticsMorphism.comp theta eta) :=
  universalResidualFamilyCompletion_composition_forced
    eta theta
    (canonicalResidualFamilyCompletion F E)
    (canonicalResidualFamilyCompletion G R)
    (canonicalResidualFamilyCompletion H Q)
    (canonicalResidualFamilyCompletion_universal F E)
    (canonicalResidualFamilyCompletionMap eta)
    (canonicalResidualFamilyCompletionMap theta)
    (canonicalResidualFamilyCompletionMap
      (FamilySemanticsMorphism.comp theta eta))

end StrongTotality
end Resolution
