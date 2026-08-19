import ResolutionStrongTotalityResidualClassification
import ResolutionStrongTotalityUnifiedMorphisms

/-!
# Exactness for structured Strong Totality

A structured Resolution Answer has two semantically distinct classes:

* realized answers, which are exactly images of certified ordinary solutions;
* residual answers, which are exactly images of values in the chosen residual
  vocabulary.

This module makes that distinction explicit and proves that it exactly tracks
ordinary satisfiability.  A specification is satisfiable exactly when some
structured answer is realized; it is unsatisfiable exactly when every
structured answer is residual.

The distinction is stable under every unified semantic morphism.  Changing the
mathematical specification and/or translating residual provenance cannot turn a
realized answer into a residual one or a residual answer into a realized one.
-/

universe u r s

namespace Resolution
namespace StrongTotality

namespace ResolutionAnswerWith

/-- A structured answer is realized when it is the canonical image of a
certified ordinary solution. -/
def IsRealized
    {S : Specification.{u}}
    {E : Type r}
    (a : ResolutionAnswerWith S E) : Prop :=
  Exists fun x : Specification.Solution S => a = realize x

/-- A structured answer is residual when it is the canonical image of a value
from the chosen residual vocabulary. -/
def IsResidual
    {S : Specification.{u}}
    {E : Type r}
    (a : ResolutionAnswerWith S E) : Prop :=
  Exists fun q : E =>
    a = (ResolutionAnswerWith.residual q : ResolutionAnswerWith S E)

/-- Every structured answer belongs to one of the two semantic classes. -/
theorem realized_or_residual
    {S : Specification.{u}}
    {E : Type r}
    (a : ResolutionAnswerWith S E) :
    IsRealized a ∨ IsResidual a := by
  cases a with
  | realized x hx =>
      exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  | residual q =>
      exact Or.inr ⟨q, rfl⟩

/-- The realized and residual classes are disjoint. -/
theorem realized_not_residual
    {S : Specification.{u}}
    {E : Type r}
    (a : ResolutionAnswerWith S E) :
    Not (IsRealized a ∧ IsResidual a) := by
  intro h
  rcases h.1 with ⟨sx, hsx⟩
  rcases h.2 with ⟨q, hq⟩
  cases sx with
  | mk x hx =>
      have hbad :
          (ResolutionAnswerWith.realized x hx : ResolutionAnswerWith S E) =
            ResolutionAnswerWith.residual q :=
        hsx.symm.trans hq
      cases hbad

end ResolutionAnswerWith

/-- Structured exactness: ordinary satisfiability is exactly the existence of a
realized structured Resolution Answer, independently of the residual
vocabulary. -/
theorem satisfiable_iff_exists_structuredRealized
    (S : Specification.{u})
    (E : Type r) :
    Specification.Satisfiable S ↔
      Exists fun a : ResolutionAnswerWith S E =>
        ResolutionAnswerWith.IsRealized a := by
  constructor
  · intro hs
    rcases hs with ⟨x, hx⟩
    let sx : Specification.Solution S := ⟨x, hx⟩
    exact ⟨ResolutionAnswerWith.realize sx, sx, rfl⟩
  · intro h
    rcases h with ⟨a, sx, _⟩
    exact ⟨sx.1, sx.2⟩

/-- Dual structured exactness: a specification is unsatisfiable exactly when
every structured Resolution Answer is residual.  This remains valid when the
residual vocabulary is empty; then the answer space is empty as well. -/
theorem not_satisfiable_iff_all_structuredResidual
    (S : Specification.{u})
    (E : Type r) :
    Not (Specification.Satisfiable S) ↔
      forall a : ResolutionAnswerWith S E,
        ResolutionAnswerWith.IsResidual a := by
  constructor
  · intro hS a
    cases a with
    | realized x hx =>
        exact False.elim (hS ⟨x, hx⟩)
    | residual q =>
        exact ⟨q, rfl⟩
  · intro hall hs
    rcases hs with ⟨x, hx⟩
    rcases hall (.realized x hx) with ⟨q, hq⟩
    cases hq

/-- Unified semantic transport preserves and reflects the realized class. -/
theorem mapAnswer_isRealized_iff
    {S T : Specification.{u}}
    {E : Type r}
    {F : Type s}
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    ResolutionAnswerWith.IsRealized (SemanticsMorphism.mapAnswer f a) ↔
      ResolutionAnswerWith.IsRealized a := by
  cases a with
  | realized x hx =>
      constructor
      · intro _
        exact ⟨⟨x, hx⟩, rfl⟩
      · intro _
        exact ⟨SpecMorphism.mapSolution f.specification ⟨x, hx⟩, rfl⟩
  | residual q =>
      constructor
      · intro h
        rcases h with ⟨sx, hsx⟩
        cases sx with
        | mk y hy =>
            cases hsx
      · intro h
        rcases h with ⟨sx, hsx⟩
        cases sx with
        | mk y hy =>
            cases hsx

/-- Unified semantic transport preserves and reflects the residual class. -/
theorem mapAnswer_isResidual_iff
    {S T : Specification.{u}}
    {E : Type r}
    {F : Type s}
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    ResolutionAnswerWith.IsResidual (SemanticsMorphism.mapAnswer f a) ↔
      ResolutionAnswerWith.IsResidual a := by
  cases a with
  | realized x hx =>
      constructor
      · intro h
        rcases h with ⟨q, hq⟩
        cases hq
      · intro h
        rcases h with ⟨q, hq⟩
        cases hq
  | residual q =>
      constructor
      · intro _
        exact ⟨q, rfl⟩
      · intro _
        exact ⟨f.residual q, rfl⟩

/-- The realized/residual partition is therefore invariant under every unified
semantic translation. -/
theorem mapAnswer_preserves_answerClass
    {S T : Specification.{u}}
    {E : Type r}
    {F : Type s}
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    (ResolutionAnswerWith.IsRealized (SemanticsMorphism.mapAnswer f a) ↔
      ResolutionAnswerWith.IsRealized a) ∧
    (ResolutionAnswerWith.IsResidual (SemanticsMorphism.mapAnswer f a) ↔
      ResolutionAnswerWith.IsResidual a) :=
  ⟨mapAnswer_isRealized_iff f a, mapAnswer_isResidual_iff f a⟩

end StrongTotality
end Resolution
