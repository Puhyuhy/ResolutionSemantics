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

This module proves the corresponding factorization property directly, without
an external category-theory dependency.  The chosen lifts are stable under
identity and composition, so the projection carries a split-fibration
structure in this elementary sense.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- An object of the total Strong Totality semantics: a mathematical
specification together with a residual vocabulary. -/
structure TotalSemanticsObject where
  specification : Specification.{u}
  Residual : Type u

namespace TotalSemanticsObject

/-- The minimal semantic object over a specification. -/
def minimal (S : Specification.{u}) : TotalSemanticsObject where
  specification := S
  Residual := Unit

/-- Reindex a semantic object along a specification morphism.  Residual
provenance is unchanged. -/
def reindex
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (B : TotalSemanticsObject)
    (hB : B.specification = T) : TotalSemanticsObject where
  specification := S
  Residual := B.Residual

end TotalSemanticsObject

/-- Morphisms in the total semantics are exactly the previously defined unified
semantic morphisms. -/
abbrev TotalSemanticsHom
    (A B : TotalSemanticsObject.{u}) : Type u :=
  SemanticsMorphism A.specification B.specification A.Residual B.Residual

namespace TotalSemanticsHom

/-- Identity total-semantics morphism. -/
def id (A : TotalSemanticsObject.{u}) : TotalSemanticsHom A A :=
  SemanticsMorphism.id A.specification A.Residual

/-- Composition in the total semantics. -/
def comp
    {A B C : TotalSemanticsObject.{u}}
    (g : TotalSemanticsHom B C)
    (f : TotalSemanticsHom A B) : TotalSemanticsHom A C :=
  SemanticsMorphism.comp g f

@[simp] theorem mapAnswer_id
    (A : TotalSemanticsObject.{u})
    (a : ResolutionAnswerWith A.specification A.Residual) :
    SemanticsMorphism.mapAnswer (id A) a = a := by
  exact SemanticsMorphism.mapAnswer_id A.specification A.Residual a

@[simp] theorem mapAnswer_comp
    {A B C : TotalSemanticsObject.{u}}
    (g : TotalSemanticsHom B C)
    (f : TotalSemanticsHom A B)
    (a : ResolutionAnswerWith A.specification A.Residual) :
    SemanticsMorphism.mapAnswer (comp g f) a =
      SemanticsMorphism.mapAnswer g (SemanticsMorphism.mapAnswer f a) := by
  exact SemanticsMorphism.mapAnswer_comp g f a

end TotalSemanticsHom

/-- Projection of a total semantic object to its mathematical specification. -/
def semanticsProjection
    (A : TotalSemanticsObject.{u}) : Specification.{u} :=
  A.specification

/-- Projection of a total semantic morphism to its specification component. -/
def semanticsProjectionMap
    {A B : TotalSemanticsObject.{u}}
    (f : TotalSemanticsHom A B) :
    SpecMorphism (semanticsProjection A) (semanticsProjection B) :=
  f.specification

/-! ## Chosen cartesian lifts -/

/-- Reindex an object over `T` along `f : S -> T`.  This formulation avoids an
extra equality witness by taking the target object explicitly to have base
specification `T`. -/
def pullbackObject
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type u) : TotalSemanticsObject where
  specification := S
  Residual := E

/-- The chosen lift from the reindexed object `(S,E)` to `(T,E)`. -/
def cartesianLift
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type u) :
    TotalSemanticsHom (pullbackObject f E)
      ({ specification := T, Residual := E } : TotalSemanticsObject) where
  specification := f
  residual := ResidualRefinement.id E

@[simp] theorem cartesianLift_projection
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type u) :
    semanticsProjectionMap (cartesianLift f E) = f := by
  rfl

/-- Given a morphism into `(T,E)` whose specification component factors through
`f : S -> T`, the residual component determines a canonical factor through the
chosen lift. -/
def cartesianFactor
    {R S T : Specification.{u}}
    {D E : Type u}
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
    {D E : Type u}
    (f : SpecMorphism S T)
    (h : SpecMorphism R S)
    (g : SemanticsMorphism R T D E) :
    (cartesianFactor f h g).residual = g.residual := by
  rfl

/-- If the base component of `g` is literally the composite `f ∘ h`, then the
chosen cartesian factor composes back to `g` on Resolution Answers.  Stating
the result at the semantic action level avoids irrelevant proof-field equality
inside `SpecMorphism`. -/
theorem cartesianLift_factorization_on_answers
    {R S T : Specification.{u}}
    {D E : Type u}
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
      simp only [SemanticsMorphism.mapAnswer]
      have hm := hbase x
      cases hm
      rfl

/-- Uniqueness of the residual part of a factor through a cartesian lift: if a
candidate factor composes to `g` on residual answers, its residual translation
must be exactly `g.residual`. -/
theorem cartesianFactor_residual_unique
    {R S T : Specification.{u}}
    {D E : Type u}
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
    | ResolutionAnswerWith.residual r => some r) he
    |> Option.some.inj

/-! ## Split stability -/

/-- Reindexing along an identity specification morphism leaves the underlying
semantic object unchanged up to definitional equality of its fields. -/
theorem pullbackObject_id_fields
    (S : Specification.{u})
    (E : Type u) :
    (pullbackObject (SpecMorphism.id S) E).specification = S ∧
      (pullbackObject (SpecMorphism.id S) E).Residual = E := by
  exact ⟨rfl, rfl⟩

/-- Reindexing residual vocabularies is strictly stable under composition: both
a one-step pullback and a two-step pullback retain exactly the same residual
type. -/
theorem pullbackObject_comp_residual
    {R S T : Specification.{u}}
    (f : SpecMorphism R S)
    (g : SpecMorphism S T)
    (E : Type u) :
    (pullbackObject (SpecMorphism.comp g f) E).Residual =
      (pullbackObject f (pullbackObject g E).Residual).Residual := by
  rfl

/-- Chosen lifts compose correctly on Resolution Answers. -/
theorem cartesianLift_comp_on_answers
    {R S T : Specification.{u}}
    (f : SpecMorphism R S)
    (g : SpecMorphism S T)
    (E : Type u)
    (a : ResolutionAnswerWith R E) :
    SemanticsMorphism.mapAnswer
        (cartesianLift (SpecMorphism.comp g f) E) a =
      SemanticsMorphism.mapAnswer (cartesianLift g E)
        (SemanticsMorphism.mapAnswer (cartesianLift f E) a) := by
  cases a <;> rfl

/-- The fiber over `S` recovered from the total semantics is exactly the
previous residual fiber: fixing `S` leaves only the residual vocabulary and its
translations. -/
def totalObjectOfFiber
    {S : Specification.{u}}
    (A : ResidualFiberObject S) : TotalSemanticsObject where
  specification := S
  Residual := A.Residual

/-- Fiber morphisms embed into the total semantics with identity base map. -/
def totalHomOfFiber
    {S : Specification.{u}}
    {A B : ResidualFiberObject S}
    (f : ResidualFiberHom A B) :
    TotalSemanticsHom (totalObjectOfFiber A) (totalObjectOfFiber B) where
  specification := SpecMorphism.id S
  residual := f

/-- The projection of every embedded fiber morphism is the identity on the base
specification. -/
@[simp] theorem totalHomOfFiber_projection
    {S : Specification.{u}}
    {A B : ResidualFiberObject S}
    (f : ResidualFiberHom A B) :
    semanticsProjectionMap (totalHomOfFiber f) = SpecMorphism.id S := by
  rfl

end StrongTotality
end Resolution
