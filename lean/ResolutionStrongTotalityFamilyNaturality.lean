import ResolutionStrongTotalityFamilyUniversal
import ResolutionStrongTotalityFunctorial

/-!
# Reindexed family naturality for Strong Totality

The family-level universal property should remain coherent when one family of
specifications is translated into another, even when the translation also
reindexes the family itself.  This module formalizes that stronger form.

A family specification morphism consists of a base map `I -> J` together with a
validity-preserving specification morphism from each source fiber `F i` to the
target fiber over its image.  A map of family completions over such a morphism
preserves all embedded ordinary solutions and residual points.

If the source family completion is universal, then for every reindexed family
translation and every target family completion there is exactly one such map.
The canonical Resolution family realizes this map by `ResolutionAnswer.map` in
each fiber.  Finally, canonical structural equivalences force the resulting
family naturality square to commute simultaneously at every index.
-/

universe u v w

namespace Resolution
namespace StrongTotality

/-- A pointed completion for every member of a specification family. -/
structure FamilyCompletionObject
    {I : Type v}
    (F : I -> Specification.{u}) where
  Carrier : I -> Type u
  includeSolution :
    (i : I) -> Specification.Solution (F i) -> Carrier i
  residual : (i : I) -> Carrier i

/-- The canonical family of Resolution completions. -/
def canonicalFamilyCompletion
    {I : Type v}
    (F : I -> Specification.{u}) : FamilyCompletionObject F where
  Carrier := fun i => ResolutionAnswer (F i)
  includeSolution := fun _ => realizeSolution
  residual := fun _ => .residual

/-- A translation between specification families may reindex the family and
translate each source specification into the corresponding target fiber. -/
structure FamilySpecMorphism
    {I : Type v}
    {J : Type w}
    (F : I -> Specification.{u})
    (G : J -> Specification.{u}) where
  index : I -> J
  mapSpec : (i : I) -> SpecMorphism (F i) (G (index i))

/-- A completion map over a reindexed family specification morphism. -/
structure FamilyCompletionHomOver
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G) where
  toFun : (i : I) -> A.Carrier i -> B.Carrier (eta.index i)
  map_solution :
    forall (i : I) (x : Specification.Solution (F i)),
      toFun i (A.includeSolution i x) =
        B.includeSolution (eta.index i)
          (SpecMorphism.mapSolution (eta.mapSpec i) x)
  map_residual :
    forall i : I,
      toFun i (A.residual i) = B.residual (eta.index i)

namespace FamilyCompletionHomOver

/-- Extensionality for maps of family completions over a fixed translation. -/
theorem ext
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    {eta : FamilySpecMorphism F G}
    {A : FamilyCompletionObject F}
    {B : FamilyCompletionObject G}
    (p q : FamilyCompletionHomOver eta A B)
    (h : forall (i : I) (x : A.Carrier i),
      p.toFun i x = q.toFun i x) :
    p = q := by
  cases p with
  | mk pto psol pres =>
      cases q with
      | mk qto qsol qres =>
          have hfun : pto = qto := by
            funext i x
            exact h i x
          cases hfun
          rfl

end FamilyCompletionHomOver

/-- The universal-family predicate specialized to a packaged family completion. -/
def IsUniversalFamilyCompletion
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F) : Prop :=
  IsUniversalTotalizationFamily F
    A.Carrier A.includeSolution A.residual

/-- The canonical family completion is globally universal. -/
theorem canonicalFamilyCompletion_universal
    {I : Type v}
    (F : I -> Specification.{u}) :
    IsUniversalFamilyCompletion F (canonicalFamilyCompletion F) :=
  resolutionAnswerFamily_isUniversalTotalization F

/-- Structural equivalence from an arbitrary family completion to the
canonical Resolution family. -/
def IsCanonicalFamilyEquiv
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F)
    (e : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i))) : Prop :=
  (forall (i : I) (x : Specification.Solution (F i)),
      e i (A.includeSolution i x) = realizeSolution x) ∧
    forall i : I,
      e i (A.residual i) =
        (ResolutionAnswer.residual : ResolutionAnswer (F i))

/-- Packaged family canonicity: every universal family completion has one
unique structural equivalence to the canonical Resolution family. -/
theorem universalFamilyCompletion_uniqueCanonicalEquiv
    {I : Type v}
    (F : I -> Specification.{u})
    (A : FamilyCompletionObject F)
    (hA : IsUniversalFamilyCompletion F A) :
    Exists fun e : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)) =>
      IsCanonicalFamilyEquiv F A e ∧
      forall g : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)),
        IsCanonicalFamilyEquiv F A g -> g = e := by
  rcases universalTotalizationFamily_unique_structural_equiv
      F A.Carrier A.includeSolution A.residual hA with
    ⟨e, he, huniq⟩
  exact ⟨e, he, huniq⟩

/-- Relative initiality for universal families, allowing arbitrary reindexing of
the base family.  Universality of the source alone forces one unique map over
any family specification translation into any pointed target family. -/
theorem universalFamilyCompletion_relativeInitial
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G)
    (hA : IsUniversalFamilyCompletion F A) :
    Exists fun p : FamilyCompletionHomOver eta A B =>
      forall q : FamilyCompletionHomOver eta A B, q = p := by
  rcases hA
      (fun i => B.Carrier (eta.index i))
      (fun i x =>
        B.includeSolution (eta.index i)
          (SpecMorphism.mapSolution (eta.mapSpec i) x))
      (fun i => B.residual (eta.index i)) with
    ⟨f, hf, huniq⟩
  let p : FamilyCompletionHomOver eta A B := {
    toFun := f
    map_solution := hf.1
    map_residual := hf.2
  }
  refine ⟨p, ?_⟩
  intro q
  have hqPreserves :
      ((forall (i : I) (x : Specification.Solution (F i)),
          q.toFun i (A.includeSolution i x) =
            B.includeSolution (eta.index i)
              (SpecMorphism.mapSolution (eta.mapSpec i) x)) ∧
        (forall i : I,
          q.toFun i (A.residual i) = B.residual (eta.index i))) :=
    ⟨q.map_solution, q.map_residual⟩
  have hqFun : q.toFun = f := huniq q.toFun hqPreserves
  apply FamilyCompletionHomOver.ext
  intro i x
  exact congrArg (fun k => k i x) hqFun

/-- The canonical map over a reindexed family translation is the fiberwise
Resolution transport. -/
def canonicalFamilyCompletionMap
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G) :
    FamilyCompletionHomOver eta
      (canonicalFamilyCompletion F)
      (canonicalFamilyCompletion G) where
  toFun := fun i => ResolutionAnswer.map (eta.mapSpec i)
  map_solution := by
    intro i x
    exact ResolutionAnswer.map_realizeSolution (eta.mapSpec i) x
  map_residual := by
    intro i
    exact ResolutionAnswer.map_residual (eta.mapSpec i)

/-- The canonical fiberwise Resolution map is exactly the unique family map
forced by the global universal property. -/
theorem canonicalFamilyCompletionMap_unique
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (q : FamilyCompletionHomOver eta
      (canonicalFamilyCompletion F)
      (canonicalFamilyCompletion G)) :
    q = canonicalFamilyCompletionMap eta := by
  rcases universalFamilyCompletion_relativeInitial
      eta (canonicalFamilyCompletion F) (canonicalFamilyCompletion G)
      (canonicalFamilyCompletion_universal F) with
    ⟨p, huniq⟩
  have hq : q = p := huniq q
  have hc : canonicalFamilyCompletionMap eta = p :=
    huniq (canonicalFamilyCompletionMap eta)
  exact hq.trans hc.symm

/-- Canonical structural equivalences force the reindexed family naturality
square to commute simultaneously in every source fiber. -/
theorem universalFamilyCompletion_naturalitySquare
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G)
    (hA : IsUniversalFamilyCompletion F A)
    (eF : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)))
    (eG : (j : J) -> Equiv (B.Carrier j) (ResolutionAnswer (G j)))
    (heF : IsCanonicalFamilyEquiv F A eF)
    (heG : IsCanonicalFamilyEquiv G B eG)
    (p : FamilyCompletionHomOver eta A B) :
    forall (i : I) (x : A.Carrier i),
      eG (eta.index i) (p.toFun i x) =
        ResolutionAnswer.map (eta.mapSpec i) (eF i x) := by
  let left : FamilyCompletionHomOver eta A (canonicalFamilyCompletion G) := {
    toFun := fun i x => eG (eta.index i) (p.toFun i x)
    map_solution := by
      intro i x
      calc
        eG (eta.index i) (p.toFun i (A.includeSolution i x)) =
            eG (eta.index i)
              (B.includeSolution (eta.index i)
                (SpecMorphism.mapSolution (eta.mapSpec i) x)) :=
          congrArg (eG (eta.index i)) (p.map_solution i x)
        _ = realizeSolution
              (SpecMorphism.mapSolution (eta.mapSpec i) x) :=
          heG.1 (eta.index i)
            (SpecMorphism.mapSolution (eta.mapSpec i) x)
    map_residual := by
      intro i
      calc
        eG (eta.index i) (p.toFun i (A.residual i)) =
            eG (eta.index i) (B.residual (eta.index i)) :=
          congrArg (eG (eta.index i)) (p.map_residual i)
        _ = (ResolutionAnswer.residual :
              ResolutionAnswer (G (eta.index i))) :=
          heG.2 (eta.index i)
  }
  let right : FamilyCompletionHomOver eta A (canonicalFamilyCompletion G) := {
    toFun := fun i x => ResolutionAnswer.map (eta.mapSpec i) (eF i x)
    map_solution := by
      intro i x
      calc
        ResolutionAnswer.map (eta.mapSpec i)
            (eF i (A.includeSolution i x)) =
            ResolutionAnswer.map (eta.mapSpec i) (realizeSolution x) :=
          congrArg (ResolutionAnswer.map (eta.mapSpec i)) (heF.1 i x)
        _ = realizeSolution
              (SpecMorphism.mapSolution (eta.mapSpec i) x) :=
          ResolutionAnswer.map_realizeSolution (eta.mapSpec i) x
    map_residual := by
      intro i
      calc
        ResolutionAnswer.map (eta.mapSpec i) (eF i (A.residual i)) =
            ResolutionAnswer.map (eta.mapSpec i)
              (ResolutionAnswer.residual : ResolutionAnswer (F i)) :=
          congrArg (ResolutionAnswer.map (eta.mapSpec i)) (heF.2 i)
        _ = (ResolutionAnswer.residual :
              ResolutionAnswer (G (eta.index i))) :=
          ResolutionAnswer.map_residual (eta.mapSpec i)
  }
  rcases universalFamilyCompletion_relativeInitial
      eta A (canonicalFamilyCompletion G) hA with
    ⟨q, huniq⟩
  have hleft : left = q := huniq left
  have hright : right = q := huniq right
  have hlr : left = right := hleft.trans hright.symm
  intro i x
  exact congrArg (fun k => k.toFun i x) hlr

/-- Coherent global canonicity and naturality.  For universal source and target
families, the unique structural equivalence of each family and the unique map
over every reindexed family translation necessarily form the canonical
Resolution naturality square. -/
theorem universalFamilies_canonicalNatural
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {G : J -> Specification.{u}}
    (eta : FamilySpecMorphism F G)
    (A : FamilyCompletionObject F)
    (B : FamilyCompletionObject G)
    (hA : IsUniversalFamilyCompletion F A)
    (hB : IsUniversalFamilyCompletion G B) :
    Exists fun eF : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)) =>
      IsCanonicalFamilyEquiv F A eF ∧
      (forall gF : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)),
        IsCanonicalFamilyEquiv F A gF -> gF = eF) ∧
      Exists fun eG : (j : J) -> Equiv (B.Carrier j) (ResolutionAnswer (G j)) =>
        IsCanonicalFamilyEquiv G B eG ∧
        (forall gG : (j : J) -> Equiv (B.Carrier j) (ResolutionAnswer (G j)),
          IsCanonicalFamilyEquiv G B gG -> gG = eG) ∧
        Exists fun p : FamilyCompletionHomOver eta A B =>
          (forall q : FamilyCompletionHomOver eta A B, q = p) ∧
          forall (i : I) (x : A.Carrier i),
            eG (eta.index i) (p.toFun i x) =
              ResolutionAnswer.map (eta.mapSpec i) (eF i x) := by
  rcases universalFamilyCompletion_uniqueCanonicalEquiv F A hA with
    ⟨eF, heF, huniqF⟩
  rcases universalFamilyCompletion_uniqueCanonicalEquiv G B hB with
    ⟨eG, heG, huniqG⟩
  rcases universalFamilyCompletion_relativeInitial eta A B hA with
    ⟨p, huniqP⟩
  refine ⟨eF, heF, huniqF, eG, heG, huniqG, p, huniqP, ?_⟩
  exact universalFamilyCompletion_naturalitySquare
    eta A B hA eF eG heF heG p

end StrongTotality
end Resolution
