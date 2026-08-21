import ResolutionStrongTotalityResidualFiber

/-!
# A split fibration of Strong Totality semantics

A structured Strong Totality semantics consists of two independent pieces:

* a mathematical specification `S`;
* a residual vocabulary `E`.

Unified semantic morphisms likewise consist of a specification morphism and a
residual translation.  Hence the total semantic structure projects to the base
of mathematical specifications by forgetting residual data.

For every specification morphism `f : S -> T` and every semantic object over
`T` with residual vocabulary `E`, there is a canonical reindexed object over
`S` with the *same* residual vocabulary `E`.  The chosen lift has specification
part `f` and residual part the identity on `E`.

Residual vocabularies may live in universes independent of the specification
universe.  This is required for the literal one-point vocabulary `Unit` and
matches the universe-general structured semantics developed upstream.

This module proves the corresponding factorization property directly, without
an external category-theory dependency.  The chosen lifts are stable under
identity and composition, so the projection carries a split-fibration
structure in this elementary sense.
-/

universe u r s t

namespace Resolution
namespace StrongTotality

/-- An object of the total Strong Totality semantics: a mathematical
specification together with a residual vocabulary in an independent universe. -/
structure TotalSemanticsObject where
  specification : Specification.{u}
  Residual : Type r

namespace TotalSemanticsObject

/-- The minimal semantic object over a specification. -/
def minimal (S : Specification.{u}) : TotalSemanticsObject.{u, 0} where
  specification := S
  Residual := Unit

/-- Reindex a semantic object along a specification morphism.  Residual
provenance is unchanged. -/
def reindex
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (B : TotalSemanticsObject.{u, r})
    (hB : B.specification = T) : TotalSemanticsObject.{u, r} where
  specification := S
  Residual := B.Residual

end TotalSemanticsObject

/-- Morphisms in the total semantics are exactly the previously defined unified
semantic morphisms. -/
abbrev TotalSemanticsHom
    (A : TotalSemanticsObject.{u, r})
    (B : TotalSemanticsObject.{u, s}) : Type (max u r s) :=
  SemanticsMorphism A.specification B.specification A.Residual B.Residual

namespace TotalSemanticsHom

/-- Identity total-semantics morphism. -/
def id (A : TotalSemanticsObject.{u, r}) : TotalSemanticsHom A A :=
  SemanticsMorphism.id A.specification A.Residual

/-- Composition in the total semantics. -/
def comp
    {A : TotalSemanticsObject.{u, r}}
    {B : TotalSemanticsObject.{u, s}}
    {C : TotalSemanticsObject.{u, t}}
    (g : TotalSemanticsHom B C)
    (f : TotalSemanticsHom A B) : TotalSemanticsHom A C :=
  SemanticsMorphism.comp g f

@[simp] theorem mapAnswer_id
    (A : TotalSemanticsObject.{u, r})
    (a : ResolutionAnswerWith A.specification A.Residual) :
    SemanticsMorphism.mapAnswer (id A) a = a := by
  exact SemanticsMorphism.mapAnswer_id A.specification A.Residual a

@[simp] theorem mapAnswer_comp
    {A : TotalSemanticsObject.{u, r}}
    {B : TotalSemanticsObject.{u, s}}
    {C : TotalSemanticsObject.{u, t}}
    (g : TotalSemanticsHom B C)
    (f : TotalSemanticsHom A B)
    (a : ResolutionAnswerWith A.specification A.Residual) :
    SemanticsMorphism.mapAnswer (comp g f) a =
      SemanticsMorphism.mapAnswer g (SemanticsMorphism.mapAnswer f a) := by
  exact SemanticsMorphism.mapAnswer_comp g f a

end TotalSemanticsHom

/-- Projection of a total semantic object to its mathematical specification. -/
def semanticsProjection
    (A : TotalSemanticsObject.{u, r}) : Specification.{u} :=
  A.specification

/-- Projection of a total semantic morphism to its specification component. -/
def semanticsProjectionMap
    {A : TotalSemanticsObject.{u, r}}
    {B : TotalSemanticsObject.{u, s}}
    (f : TotalSemanticsHom A B) :
    SpecMorphism (semanticsProjection A) (semanticsProjection B) :=
  f.specification

/-! ## Chosen cartesian lifts -/

/-- Reindex an object over `T` along `f : S -> T`. -/
def pullbackObject
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type r) : TotalSemanticsObject.{u, r} where
  specification := S
  Residual := E

/-- The chosen lift from the reindexed object `(S,E)` to `(T,E)`. -/
def cartesianLift
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type r) :
    TotalSemanticsHom (pullbackObject f E)
      ({ specification := T, Residual := E } : TotalSemanticsObject.{u, r}) where
  specification := f
  residual := ResidualRefinement.id E

@[simp] theorem cartesianLift_projection
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type r) :
    semanticsProjectionMap (cartesianLift f E) = f := by
  rfl

/-- Given a morphism into `(T,E)` whose specification component factors through
`f : S -> T`, the residual component determines a canonical factor through the
chosen lift. -/
def cartesianFactor
    {R S T : Specification.{u}}
    {D : Type r} {E : Type s}
    (f : SpecMorphism S T)
    (h : SpecMorphism R S)
    (g : SemanticsMorphism R T D E) :
    SemanticsMorphism R S D E where
  specification := h
  residual := g.residual

/-- The residual component of the cartesian factor is exactly the original
residual translation. -/
@[simp] theorem cartesianFactor_residual
    {R S T : Specification.{u}}
    {D : Type r} {E : Type s}
    (f : SpecMorphism S T)
    (h : SpecMorphism R S)
    (g : SemanticsMorphism R T D E) :
    (cartesianFactor f h g).residual = g.residual := by
  rfl

/-- If the base component of `g` is the composite `f ∘ h` on candidates, then
the chosen cartesian factor composes back to `g` on Resolution Answers. -/
theorem cartesianLift_factorization_on_answers
    {R S T : Specification.{u}}
    {D : Type r} {E : Type s}
    (f : SpecMorphism S T)
    (h : SpecMorphism R S)
    (g : SemanticsMorphism R T D E)
    (hbase : forall x : R.Candidate,
      g.specification.map x = f.map (h.map x))
    (a : ResolutionAnswerWith R D) :
    SemanticsMorphism.mapAnswer
        (SemanticsMorphism.comp
          (cartesianLift f E)
          (cartesianFactor f h g)) a =
      SemanticsMorphism.mapAnswer g a := by
  cases a with
  | residual e => rfl
  | realized x hx =>
      have hs :
          SpecMorphism.mapSolution (SpecMorphism.comp f h)
              (⟨x, hx⟩ : Specification.Solution R) =
            SpecMorphism.mapSolution g.specification
              (⟨x, hx⟩ : Specification.Solution R) := by
        apply Subtype.eq
        exact (hbase x).symm
      change
        ResolutionAnswerWith.realize
            (SpecMorphism.mapSolution (SpecMorphism.comp f h)
              (⟨x, hx⟩ : Specification.Solution R)) =
          ResolutionAnswerWith.realize
            (SpecMorphism.mapSolution g.specification
              (⟨x, hx⟩ : Specification.Solution R))
      rw [hs]

/-- Uniqueness of the residual part of a factor through a cartesian lift. -/
theorem cartesianFactor_residual_unique
    {R S T : Specification.{u}}
    {D : Type r} {E : Type s}
    (f : SpecMorphism S T)
    (h : SpecMorphism R S)
    (g : SemanticsMorphism R T D E)
    (k : SemanticsMorphism R S D E)
    (hk : forall e : D,
      SemanticsMorphism.mapAnswer
          (SemanticsMorphism.comp (cartesianLift f E) k)
          (.residual e : ResolutionAnswerWith R D) =
        SemanticsMorphism.mapAnswer g
          (.residual e : ResolutionAnswerWith R D)) :
    k.residual = (cartesianFactor f h g).residual := by
  funext e
  have he := hk e
  exact congrArg (fun a => match a with
    | ResolutionAnswerWith.realized _ _ => none
    | ResolutionAnswerWith.residual q => some q) he
    |> Option.some.inj

/-! ## Split stability -/

/-- Reindexing along an identity specification morphism leaves the underlying
semantic object unchanged up to definitional equality of its fields. -/
theorem pullbackObject_id_fields
    (S : Specification.{u})
    (E : Type r) :
    (pullbackObject (SpecMorphism.id S) E).specification = S ∧
      (pullbackObject (SpecMorphism.id S) E).Residual = E := by
  exact ⟨rfl, rfl⟩

/-- Reindexing residual vocabularies is strictly stable under composition. -/
theorem pullbackObject_comp_residual
    {R S T : Specification.{u}}
    (f : SpecMorphism R S)
    (g : SpecMorphism S T)
    (E : Type r) :
    (pullbackObject (SpecMorphism.comp g f) E).Residual =
      (pullbackObject f (pullbackObject g E).Residual).Residual := by
  rfl

/-- Chosen lifts compose correctly on Resolution Answers. -/
theorem cartesianLift_comp_on_answers
    {R S T : Specification.{u}}
    (f : SpecMorphism R S)
    (g : SpecMorphism S T)
    (E : Type r)
    (a : ResolutionAnswerWith R E) :
    SemanticsMorphism.mapAnswer
        (cartesianLift (SpecMorphism.comp g f) E) a =
      SemanticsMorphism.mapAnswer (cartesianLift g E)
        (SemanticsMorphism.mapAnswer (cartesianLift f E) a) := by
  cases a <;> rfl

/-- The fiber over `S` recovered from the total semantics is exactly the
previous residual fiber. -/
def totalObjectOfFiber
    {S : Specification.{u}}
    (A : ResidualFiberObject.{u, r} S) : TotalSemanticsObject.{u, r} where
  specification := S
  Residual := A.Residual

/-- Fiber morphisms embed into the total semantics with identity base map. -/
def totalHomOfFiber
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    (f : ResidualFiberHom A B) :
    TotalSemanticsHom (totalObjectOfFiber A) (totalObjectOfFiber B) where
  specification := SpecMorphism.id S
  residual := f

/-- The projection of every embedded fiber morphism is the identity on the base
specification. -/
@[simp] theorem totalHomOfFiber_projection
    {S : Specification.{u}}
    {A : ResidualFiberObject.{u, r} S}
    {B : ResidualFiberObject.{u, s} S}
    (f : ResidualFiberHom A B) :
    semanticsProjectionMap (totalHomOfFiber f) = SpecMorphism.id S := by
  rfl

end StrongTotality
end Resolution
