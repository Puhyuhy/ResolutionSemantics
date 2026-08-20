import ResolutionStrongTotalityFamilyResidual
import ResolutionStrongTotalityUnifiedMorphisms

/-!
# Reindexed naturality for structured residual families

Family-level structured Strong Totality must transport both kinds of semantic
data simultaneously: ordinary solutions follow specification morphisms, while
residual provenance follows residual refinements.  The family may also be
reindexed.

This module packages that translation, proves the induced canonical transport
on `ResolutionAnswerWith`, and shows that the global universal property forces
that transport uniquely.  Thus provenance-aware family naturality is not an
extra implementation choice: it is determined by Strong Totality itself.
-/

universe u r v w z

namespace Resolution
namespace StrongTotality

/-- A packaged structured completion in every fiber of a specification family. -/
structure ResidualFamilyCompletionObject
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r) where
  Carrier : I -> Type (max u r)
  includeSolution :
    (i : I) -> Specification.Solution (F i) -> Carrier i
  includeResidual : (i : I) -> E i -> Carrier i

/-- The canonical structured Resolution family. -/
def canonicalResidualFamilyCompletion
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r) : ResidualFamilyCompletionObject F E where
  Carrier := fun i => ResolutionAnswerWith (F i) (E i)
  includeSolution := fun _ => ResolutionAnswerWith.realize
  includeResidual := fun _ q => .residual q

/-- A reindexed translation of structured families transports both the
specification and its residual vocabulary in every source fiber. -/
structure FamilySemanticsMorphism
    {I : Type v}
    {J : Type w}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (G : J -> Specification.{u})
    (R : J -> Type r) where
  index : I -> J
  specification :
    (i : I) -> SpecMorphism (F i) (G (index i))
  residual : (i : I) -> ResidualRefinement (E i) (R (index i))

namespace FamilySemanticsMorphism

/-- Identity translation of a structured family. -/
def id
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r) : FamilySemanticsMorphism F E F E where
  index := fun i => i
  specification := fun i => SpecMorphism.id (F i)
  residual := fun i => ResidualRefinement.id (E i)

/-- Composition of reindexed structured-family translations. -/
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
    (theta : FamilySemanticsMorphism G R H Q)
    (eta : FamilySemanticsMorphism F E G R) :
    FamilySemanticsMorphism F E H Q where
  index := fun i => theta.index (eta.index i)
  specification := fun i =>
    SpecMorphism.comp
      (theta.specification (eta.index i))
      (eta.specification i)
  residual := fun i =>
    ResidualRefinement.comp
      (theta.residual (eta.index i))
      (eta.residual i)

/-- The ordinary single-fiber semantic morphism underlying a family
translation at one source index. -/
def fiber
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (i : I) :
    SemanticsMorphism (F i) (G (eta.index i))
      (E i) (R (eta.index i)) where
  specification := eta.specification i
  residual := eta.residual i

/-- Canonical structured Resolution transport along a family translation. -/
def mapAnswer
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (i : I) :
    ResolutionAnswerWith (F i) (E i) ->
      ResolutionAnswerWith (G (eta.index i)) (R (eta.index i)) :=
  SemanticsMorphism.mapAnswer (fiber eta i)

@[simp] theorem mapAnswer_realize
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (i : I)
    (x : Specification.Solution (F i)) :
    mapAnswer eta i (ResolutionAnswerWith.realize x) =
      ResolutionAnswerWith.realize
        (SpecMorphism.mapSolution (eta.specification i) x) := by
  exact SemanticsMorphism.mapAnswer_realize (fiber eta i) x

@[simp] theorem mapAnswer_residual
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (i : I)
    (q : E i) :
    mapAnswer eta i (ResolutionAnswerWith.residual q) =
      (ResolutionAnswerWith.residual (eta.residual i q) :
        ResolutionAnswerWith (G (eta.index i)) (R (eta.index i))) := by
  exact SemanticsMorphism.mapAnswer_residual (fiber eta i) q

@[simp] theorem mapAnswer_id
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (i : I)
    (a : ResolutionAnswerWith (F i) (E i)) :
    mapAnswer (id F E) i a = a := by
  exact SemanticsMorphism.mapAnswer_id (F i) (E i) a

@[simp] theorem mapAnswer_comp
    {I : Type v}
    {J : Type w}
    {K : Type z}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    {H : K -> Specification.{u}}
    {Q : K -> Type r}
    (theta : FamilySemanticsMorphism G R H Q)
    (eta : FamilySemanticsMorphism F E G R)
    (i : I)
    (a : ResolutionAnswerWith (F i) (E i)) :
    mapAnswer (comp theta eta) i a =
      mapAnswer theta (eta.index i) (mapAnswer eta i a) := by
  exact SemanticsMorphism.mapAnswer_comp
    (fiber theta (eta.index i)) (fiber eta i) a

end FamilySemanticsMorphism

/-- A structured completion map over a reindexed semantic family translation. -/
structure ResidualFamilyCompletionHomOver
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (A : ResidualFamilyCompletionObject F E)
    (B : ResidualFamilyCompletionObject G R) where
  toFun : (i : I) -> A.Carrier i -> B.Carrier (eta.index i)
  map_solution :
    forall (i : I) (x : Specification.Solution (F i)),
      toFun i (A.includeSolution i x) =
        B.includeSolution (eta.index i)
          (SpecMorphism.mapSolution (eta.specification i) x)
  map_residual :
    forall (i : I) (q : E i),
      toFun i (A.includeResidual i q) =
        B.includeResidual (eta.index i) (eta.residual i q)

namespace ResidualFamilyCompletionHomOver

/-- Extensionality for structured family completion maps. -/
theorem ext
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    {eta : FamilySemanticsMorphism F E G R}
    {A : ResidualFamilyCompletionObject F E}
    {B : ResidualFamilyCompletionObject G R}
    (p q : ResidualFamilyCompletionHomOver eta A B)
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

end ResidualFamilyCompletionHomOver

/-- The global residual-family universal property for a packaged completion. -/
def IsUniversalResidualFamilyCompletion
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (A : ResidualFamilyCompletionObject F E) : Prop :=
  IsUniversalResidualExtensionFamily F E
    A.Carrier A.includeSolution A.includeResidual

/-- The canonical structured Resolution family is globally universal. -/
theorem canonicalResidualFamilyCompletion_universal
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r) :
    IsUniversalResidualFamilyCompletion F E
      (canonicalResidualFamilyCompletion F E) :=
  resolutionAnswerWithFamily_isUniversalResidualExtension F E

/-- Universality of the source forces one unique map over every reindexed
structured-family translation into every target completion. -/
theorem universalResidualFamilyCompletion_relativeInitial
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (A : ResidualFamilyCompletionObject F E)
    (B : ResidualFamilyCompletionObject G R)
    (hA : IsUniversalResidualFamilyCompletion F E A) :
    Exists fun p : ResidualFamilyCompletionHomOver eta A B =>
      forall q : ResidualFamilyCompletionHomOver eta A B, q = p := by
  rcases hA
      (fun i => B.Carrier (eta.index i))
      (fun i x =>
        B.includeSolution (eta.index i)
          (SpecMorphism.mapSolution (eta.specification i) x))
      (fun i q =>
        B.includeResidual (eta.index i) (eta.residual i q)) with
    ⟨f, hf, hUnique⟩
  let p : ResidualFamilyCompletionHomOver eta A B := {
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
              (SpecMorphism.mapSolution (eta.specification i) x)) ∧
        (forall (i : I) (e : E i),
          q.toFun i (A.includeResidual i e) =
            B.includeResidual (eta.index i) (eta.residual i e))) :=
    ⟨q.map_solution, q.map_residual⟩
  have hqFun : q.toFun = f := hUnique q.toFun hqPreserves
  apply ResidualFamilyCompletionHomOver.ext
  intro i x
  exact congrArg (fun k => k i x) hqFun

/-- The canonical map over a structured family translation is the fiberwise
unified semantic transport. -/
def canonicalResidualFamilyCompletionMap
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R) :
    ResidualFamilyCompletionHomOver eta
      (canonicalResidualFamilyCompletion F E)
      (canonicalResidualFamilyCompletion G R) where
  toFun := fun i => FamilySemanticsMorphism.mapAnswer eta i
  map_solution := by
    intro i x
    exact FamilySemanticsMorphism.mapAnswer_realize eta i x
  map_residual := by
    intro i q
    exact FamilySemanticsMorphism.mapAnswer_residual eta i q

/-- The canonical provenance-aware family transport is exactly the unique map
forced by Strong Totality. -/
theorem canonicalResidualFamilyCompletionMap_unique
    {I : Type v}
    {J : Type w}
    {F : I -> Specification.{u}}
    {E : I -> Type r}
    {G : J -> Specification.{u}}
    {R : J -> Type r}
    (eta : FamilySemanticsMorphism F E G R)
    (q : ResidualFamilyCompletionHomOver eta
      (canonicalResidualFamilyCompletion F E)
      (canonicalResidualFamilyCompletion G R)) :
    q = canonicalResidualFamilyCompletionMap eta := by
  rcases universalResidualFamilyCompletion_relativeInitial
      eta
      (canonicalResidualFamilyCompletion F E)
      (canonicalResidualFamilyCompletion G R)
      (canonicalResidualFamilyCompletion_universal F E) with
    ⟨p, hUnique⟩
  have hq : q = p := hUnique q
  have hc : canonicalResidualFamilyCompletionMap eta = p :=
    hUnique (canonicalResidualFamilyCompletionMap eta)
  exact hq.trans hc.symm

end StrongTotality
end Resolution
