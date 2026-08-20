import ResolutionStrongTotalityFamilyInitiality

/-!
# Coherence laws forced by family Strong Totality

The family-level universal property does more than provide maps: it forces all
compatible maps with a universal source to coincide.  Consequently identity and
composition laws for the canonical Resolution family are consequences of
universality itself, rather than separate implementation facts about
`ResolutionAnswer.map`.

This module equips reindexed family specification morphisms and family
completion maps with composition, proves the general uniqueness principle for
maps out of a universal family completion, and derives canonical identity and
composition from that uniqueness.
-/

universe u v w z

namespace Resolution
namespace StrongTotality

namespace FamilySpecMorphism

/-- Composition of reindexed family specification morphisms. -/
def comp
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    {H : K -> Specification.{u}}
    (theta : FamilySpecMorphism G H)
    (eta : FamilySpecMorphism F G) : FamilySpecMorphism F H where
  index := fun i => theta.index (eta.index i)
  mapSpec := fun i =>
    SpecMorphism.comp (theta.mapSpec (eta.index i)) (eta.mapSpec i)

end FamilySpecMorphism

namespace FamilyCompletionHomOver

/-- Identity map of a family completion, lying over the identity translation of
the underlying specification family. -/
def id
    {I : Type v}
    {F : I -> Specification.{u}}
    (A : FamilyCompletionObject F) :
    FamilyCompletionHomOver (FamilySpecMorphism.id F) A A where
  toFun := fun _ x => x
  map_solution := by
    intro i x
    change A.includeSolution i x =
      A.includeSolution i
        (SpecMorphism.mapSolution (SpecMorphism.id (F i)) x)
    exact congrArg (A.includeSolution i)
      (SpecMorphism.mapSolution_id (F i) x).symm
  map_residual := by
    intro i
    rfl

/-- Composition of family completion maps over composable reindexed family
translations. -/
def comp
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    {H : K -> Specification.{u}}
    {eta : FamilySpecMorphism F G}
    {theta : FamilySpecMorphism G H}
    {A : FamilyCompletionObject F}
    {B : FamilyCompletionObject G}
    {C : FamilyCompletionObject H}
    (q : FamilyCompletionHomOver theta B C)
    (p : FamilyCompletionHomOver eta A B) :
    FamilyCompletionHomOver (FamilySpecMorphism.comp theta eta) A C where
  toFun := fun i x => q.toFun (eta.index i) (p.toFun i x)
  map_solution := by
    intro i x
    change q.toFun (eta.index i) (p.toFun i (A.includeSolution i x)) =
      C.includeSolution (theta.index (eta.index i))
        (SpecMorphism.mapSolution
          (SpecMorphism.comp
            (theta.mapSpec (eta.index i)) (eta.mapSpec i)) x)
    calc
      q.toFun (eta.index i) (p.toFun i (A.includeSolution i x)) =
          q.toFun (eta.index i)
            (B.includeSolution (eta.index i)
              (SpecMorphism.mapSolution (eta.mapSpec i) x)) :=
        congrArg (q.toFun (eta.index i)) (p.map_solution i x)
      _ = C.includeSolution (theta.index (eta.index i))
            (SpecMorphism.mapSolution (theta.mapSpec (eta.index i))
              (SpecMorphism.mapSolution (eta.mapSpec i) x)) :=
        q.map_solution (eta.index i)
          (SpecMorphism.mapSolution (eta.mapSpec i) x)
      _ = C.includeSolution (theta.index (eta.index i))
            (SpecMorphism.mapSolution
              (SpecMorphism.comp
                (theta.mapSpec (eta.index i)) (eta.mapSpec i)) x) :=
        congrArg (C.includeSolution (theta.index (eta.index i)))
          (SpecMorphism.mapSolution_comp
            (theta.mapSpec (eta.index i)) (eta.mapSpec i) x).symm
  map_residual := by
    intro i
    change q.toFun (eta.index i) (p.toFun i (A.residual i)) =
      C.residual (theta.index (eta.index i))
    calc
      q.toFun (eta.index i) (p.toFun i (A.residual i)) =
          q.toFun (eta.index i) (B.residual (eta.index i)) :=
        congrArg (q.toFun (eta.index i)) (p.map_residual i)
      _ = C.residual (theta.index (eta.index i)) :=
        q.map_residual (eta.index i)

end FamilyCompletionHomOver

/-- Any two maps over the same family translation out of a universal family
completion are equal.  This is the basic coherence engine for all subsequent
laws. -/
theorem universalFamilyCompletion_homOver_subsingleton
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G)
    (hA : IsUniversalFamilyCompletion F A)
    (p q : FamilyCompletionHomOver eta A B) :
    p = q := by
  rcases universalFamilyCompletion_relativeInitial eta A B hA with
    ⟨r, hUnique⟩
  exact (hUnique p).trans (hUnique q).symm

/-- For a universal family completion, every endomorphism over the identity
translation is forced to be the identity completion map. -/
theorem universalFamilyCompletion_identity_forced
    {I : Type v}
    {F : I -> Specification.{u}}
    (A : FamilyCompletionObject F)
    (hA : IsUniversalFamilyCompletion F A)
    (p : FamilyCompletionHomOver (FamilySpecMorphism.id F) A A) :
    p = FamilyCompletionHomOver.id A :=
  universalFamilyCompletion_homOver_subsingleton
    (FamilySpecMorphism.id F) A A hA p (FamilyCompletionHomOver.id A)

/-- Composition is forced by universality: any composable pair of family
completion maps out of a universal source has composite equal to every other
map over the composite family translation. -/
theorem universalFamilyCompletion_composition_forced
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    {H : K -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (theta : FamilySpecMorphism G H)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G)
    (C : FamilyCompletionObject H)
    (hA : IsUniversalFamilyCompletion F A)
    (p : FamilyCompletionHomOver eta A B)
    (q : FamilyCompletionHomOver theta B C)
    (r : FamilyCompletionHomOver (FamilySpecMorphism.comp theta eta) A C) :
    FamilyCompletionHomOver.comp q p = r :=
  universalFamilyCompletion_homOver_subsingleton
    (FamilySpecMorphism.comp theta eta) A C hA
      (FamilyCompletionHomOver.comp q p) r

/-- The canonical family map over the identity translation is the identity map.
The proof uses only universal uniqueness, not a pointwise case split on
Resolution Answers. -/
theorem canonicalFamilyCompletionMap_id
    {I : Type v}
    (F : I -> Specification.{u}) :
    canonicalFamilyCompletionMap (FamilySpecMorphism.id F) =
      FamilyCompletionHomOver.id (canonicalFamilyCompletion F) :=
  universalFamilyCompletion_identity_forced
    (canonicalFamilyCompletion F)
    (canonicalFamilyCompletion_universal F)
    (canonicalFamilyCompletionMap (FamilySpecMorphism.id F))

/-- Canonical Resolution transport preserves composition because the universal
family property forces the composite map to be the unique map over the
composite translation. -/
theorem canonicalFamilyCompletionMap_comp
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    {H : K -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (theta : FamilySpecMorphism G H) :
    FamilyCompletionHomOver.comp
        (canonicalFamilyCompletionMap theta)
        (canonicalFamilyCompletionMap eta) =
      canonicalFamilyCompletionMap (FamilySpecMorphism.comp theta eta) :=
  universalFamilyCompletion_composition_forced
    eta theta
    (canonicalFamilyCompletion F)
    (canonicalFamilyCompletion G)
    (canonicalFamilyCompletion H)
    (canonicalFamilyCompletion_universal F)
    (canonicalFamilyCompletionMap eta)
    (canonicalFamilyCompletionMap theta)
    (canonicalFamilyCompletionMap (FamilySpecMorphism.comp theta eta))

end StrongTotality
end Resolution
