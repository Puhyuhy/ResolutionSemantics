import ResolutionStrongTotalityFamilyResidualNaturality
import ResolutionStrongTotalityFamilyCoherence

/-!
# Canonical conjugation formulas for universal family maps

Naturality says that canonical structural equivalences make the relevant square
commute.  The stronger computational statement solves that square explicitly:
every map out of a universal family completion is the canonical Resolution
transport conjugated by the unique structural equivalences.

For the one-residual theory this has the form

  p_i = e_G(i)⁻¹ ∘ ResolutionAnswer.map(eta_i) ∘ e_F(i).

For structured residual provenance, `ResolutionAnswer.map` is replaced by the
unified semantic transport which moves both ordinary solutions and residual
provenance.  These formulas classify the maps themselves, not merely their
action on generators.
-/

universe u r v w

namespace Resolution
namespace StrongTotality

/-- Every map over a reindexed family translation out of a universal source is
literally canonical Resolution transport conjugated by structural equivalences
to the canonical source and target families. -/
theorem universalFamilyCompletion_map_eq_canonicalConjugate
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
      p.toFun i x =
        (eG (eta.index i)).symm
          (ResolutionAnswer.map (eta.mapSpec i) (eF i x)) := by
  intro i x
  apply (eG (eta.index i)).injective
  calc
    eG (eta.index i) (p.toFun i x) =
        ResolutionAnswer.map (eta.mapSpec i) (eF i x) :=
      universalFamilyCompletion_naturalitySquare
        eta A B hA eF eG heF heG p i x
    _ = eG (eta.index i)
          ((eG (eta.index i)).symm
            (ResolutionAnswer.map (eta.mapSpec i) (eF i x))) :=
      ((eG (eta.index i)).right_inv
        (ResolutionAnswer.map (eta.mapSpec i) (eF i x))).symm

/-- Fully packaged minimal-family classification: unique source and target
canonical equivalences and the unique map over `eta` exist simultaneously, and
the map is exactly canonical transport conjugated by those equivalences. -/
theorem universalFamilies_canonicalConjugate
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
            p.toFun i x =
              (eG (eta.index i)).symm
                (ResolutionAnswer.map (eta.mapSpec i) (eF i x)) := by
  rcases universalFamilies_canonicalNatural eta A B hA hB with
    ⟨eF, heF, huniqF, eG, heG, huniqG, p, huniqP, _⟩
  refine ⟨eF, heF, huniqF, eG, heG, huniqG, p, huniqP, ?_⟩
  exact universalFamilyCompletion_map_eq_canonicalConjugate
    eta A B hA eF eG heF heG p

/-- Structural equivalence for a packaged residual-family completion. -/
def IsCanonicalResidualFamilyEquiv
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (A : ResidualFamilyCompletionObject F E)
    (e : (i : I) ->
      Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i))) : Prop :=
  IsStructuralResidualFamilyEquiv
    F E A.Carrier A.includeSolution A.includeResidual e

/-- Packaged structured-family canonicity. -/
theorem universalResidualFamilyCompletion_uniqueCanonicalEquiv
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (A : ResidualFamilyCompletionObject F E)
    (hA : IsUniversalResidualFamilyCompletion F E A) :
    Exists fun e : (i : I) ->
        Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)) =>
      IsCanonicalResidualFamilyEquiv F E A e ∧
      forall g : (i : I) ->
          Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)),
        IsCanonicalResidualFamilyEquiv F E A g -> g = e := by
  exact universalResidualExtensionFamily_unique_structural_equiv
    F E A.Carrier A.includeSolution A.includeResidual hA

/-- Structured canonical equivalences force the provenance-aware reindexed
naturality square to commute in every source fiber. -/
theorem universalResidualFamilyCompletion_naturalitySquare
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
    (eF : (i : I) ->
      Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)))
    (eG : (j : J) ->
      Equiv (B.Carrier j) (ResolutionAnswerWith (G j) (R j)))
    (heF : IsCanonicalResidualFamilyEquiv F E A eF)
    (heG : IsCanonicalResidualFamilyEquiv G R B eG)
    (p : ResidualFamilyCompletionHomOver eta A B) :
    forall (i : I) (x : A.Carrier i),
      eG (eta.index i) (p.toFun i x) =
        FamilySemanticsMorphism.mapAnswer eta i (eF i x) := by
  let left : ResidualFamilyCompletionHomOver eta A
      (canonicalResidualFamilyCompletion G R) := {
    toFun := fun i x => eG (eta.index i) (p.toFun i x)
    map_solution := by
      intro i x
      calc
        eG (eta.index i) (p.toFun i (A.includeSolution i x)) =
            eG (eta.index i)
              (B.includeSolution (eta.index i)
                (SpecMorphism.mapSolution (eta.specification i) x)) :=
          congrArg (eG (eta.index i)) (p.map_solution i x)
        _ = ResolutionAnswerWith.realize
              (SpecMorphism.mapSolution (eta.specification i) x) :=
          heG.1 (eta.index i)
            (SpecMorphism.mapSolution (eta.specification i) x)
    map_residual := by
      intro i q
      calc
        eG (eta.index i) (p.toFun i (A.includeResidual i q)) =
            eG (eta.index i)
              (B.includeResidual (eta.index i) (eta.residual i q)) :=
          congrArg (eG (eta.index i)) (p.map_residual i q)
        _ = (ResolutionAnswerWith.residual (eta.residual i q) :
              ResolutionAnswerWith
                (G (eta.index i)) (R (eta.index i))) :=
          heG.2 (eta.index i) (eta.residual i q)
  }
  let right : ResidualFamilyCompletionHomOver eta A
      (canonicalResidualFamilyCompletion G R) := {
    toFun := fun i x => FamilySemanticsMorphism.mapAnswer eta i (eF i x)
    map_solution := by
      intro i x
      calc
        FamilySemanticsMorphism.mapAnswer eta i
            (eF i (A.includeSolution i x)) =
            FamilySemanticsMorphism.mapAnswer eta i
              (ResolutionAnswerWith.realize x) :=
          congrArg (FamilySemanticsMorphism.mapAnswer eta i) (heF.1 i x)
        _ = ResolutionAnswerWith.realize
              (SpecMorphism.mapSolution (eta.specification i) x) :=
          FamilySemanticsMorphism.mapAnswer_realize eta i x
    map_residual := by
      intro i q
      calc
        FamilySemanticsMorphism.mapAnswer eta i
            (eF i (A.includeResidual i q)) =
            FamilySemanticsMorphism.mapAnswer eta i
              (ResolutionAnswerWith.residual q) :=
          congrArg (FamilySemanticsMorphism.mapAnswer eta i) (heF.2 i q)
        _ = (ResolutionAnswerWith.residual (eta.residual i q) :
              ResolutionAnswerWith
                (G (eta.index i)) (R (eta.index i))) :=
          FamilySemanticsMorphism.mapAnswer_residual eta i q
  }
  rcases universalResidualFamilyCompletion_relativeInitial
      eta A (canonicalResidualFamilyCompletion G R) hA with
    ⟨q, hUnique⟩
  have hleft : left = q := hUnique left
  have hright : right = q := hUnique right
  have hlr : left = right := hleft.trans hright.symm
  intro i x
  exact congrArg (fun k => k.toFun i x) hlr

/-- Every provenance-aware map out of a universal residual family is exactly the
canonical unified semantic transport conjugated by structural equivalences. -/
theorem universalResidualFamilyCompletion_map_eq_canonicalConjugate
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
    (eF : (i : I) ->
      Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)))
    (eG : (j : J) ->
      Equiv (B.Carrier j) (ResolutionAnswerWith (G j) (R j)))
    (heF : IsCanonicalResidualFamilyEquiv F E A eF)
    (heG : IsCanonicalResidualFamilyEquiv G R B eG)
    (p : ResidualFamilyCompletionHomOver eta A B) :
    forall (i : I) (x : A.Carrier i),
      p.toFun i x =
        (eG (eta.index i)).symm
          (FamilySemanticsMorphism.mapAnswer eta i (eF i x)) := by
  intro i x
  apply (eG (eta.index i)).injective
  calc
    eG (eta.index i) (p.toFun i x) =
        FamilySemanticsMorphism.mapAnswer eta i (eF i x) :=
      universalResidualFamilyCompletion_naturalitySquare
        eta A B hA eF eG heF heG p i x
    _ = eG (eta.index i)
          ((eG (eta.index i)).symm
            (FamilySemanticsMorphism.mapAnswer eta i (eF i x))) :=
      ((eG (eta.index i)).right_inv
        (FamilySemanticsMorphism.mapAnswer eta i (eF i x))).symm

/-- Fully packaged provenance-aware classification: the unique structural
source and target equivalences and unique map over a reindexed semantic
translation exist simultaneously, and the map is their canonical conjugate. -/
theorem universalResidualFamilies_canonicalConjugate
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
    (hB : IsUniversalResidualFamilyCompletion G R B) :
    Exists fun eF : (i : I) ->
        Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)) =>
      IsCanonicalResidualFamilyEquiv F E A eF ∧
      (forall gF : (i : I) ->
          Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)),
        IsCanonicalResidualFamilyEquiv F E A gF -> gF = eF) ∧
      Exists fun eG : (j : J) ->
          Equiv (B.Carrier j) (ResolutionAnswerWith (G j) (R j)) =>
        IsCanonicalResidualFamilyEquiv G R B eG ∧
        (forall gG : (j : J) ->
            Equiv (B.Carrier j) (ResolutionAnswerWith (G j) (R j)),
          IsCanonicalResidualFamilyEquiv G R B gG -> gG = eG) ∧
        Exists fun p : ResidualFamilyCompletionHomOver eta A B =>
          (forall q : ResidualFamilyCompletionHomOver eta A B, q = p) ∧
          forall (i : I) (x : A.Carrier i),
            p.toFun i x =
              (eG (eta.index i)).symm
                (FamilySemanticsMorphism.mapAnswer eta i (eF i x)) := by
  rcases universalResidualFamilyCompletion_uniqueCanonicalEquiv
      F E A hA with
    ⟨eF, heF, huniqF⟩
  rcases universalResidualFamilyCompletion_uniqueCanonicalEquiv
      G R B hB with
    ⟨eG, heG, huniqG⟩
  rcases universalResidualFamilyCompletion_relativeInitial eta A B hA with
    ⟨p, huniqP⟩
  refine ⟨eF, heF, huniqF, eG, heG, huniqG, p, huniqP, ?_⟩
  exact universalResidualFamilyCompletion_map_eq_canonicalConjugate
    eta A B hA eF eG heF heG p

end StrongTotality
end Resolution
