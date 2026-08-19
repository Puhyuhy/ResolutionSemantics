import ResolutionStrongTotalityResidualRefinement

/-!
# Unified morphisms for Strong Totality semantics

There are two independent ways to transport a Strong Totality semantics:

* translate the mathematical specification by a validity-preserving
  `SpecMorphism`;
* translate the residual vocabulary by a residual refinement `E -> F`.

This module packages both operations into one semantic morphism.  The induced
map on structured Resolution Answers transports realized solutions through the
specification map and residual answers through the residual map.  Identity and
composition laws hold definitionally on answers.

The two axes commute, and forgetting residual provenance is natural with
respect to arbitrary specification translations.  Consequently the minimal
one-residual semantics is not only terminal in each fixed-specification fiber;
the terminal coarsening is compatible with change of mathematical
specification.
-/

universe u r s t

namespace Resolution
namespace StrongTotality

/-- A morphism between structured Strong Totality semantics simultaneously
translates the mathematical specification and the residual vocabulary.
The residual source and target may live in universes independent of the
specification universe. -/
structure SemanticsMorphism
    (S T : Specification.{u})
    (E : Type r) (F : Type s) where
  specification : SpecMorphism S T
  residual : ResidualRefinement E F

namespace SemanticsMorphism

/-- Identity semantic translation. -/
def id
    (S : Specification.{u})
    (E : Type r) : SemanticsMorphism S S E E where
  specification := SpecMorphism.id S
  residual := ResidualRefinement.id E

/-- Composition of semantic translations. -/
def comp
    {S T U : Specification.{u}}
    {E : Type r} {F : Type s} {G : Type t}
    (g : SemanticsMorphism T U F G)
    (f : SemanticsMorphism S T E F) :
    SemanticsMorphism S U E G where
  specification := SpecMorphism.comp g.specification f.specification
  residual := ResidualRefinement.comp g.residual f.residual

/-- Transport a structured Resolution Answer along a unified semantic
morphism. -/
def mapAnswer
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F) :
    ResolutionAnswerWith S E -> ResolutionAnswerWith T F
  | .realized x hx =>
      .realized (f.specification.map x)
        (f.specification.preserves x hx)
  | .residual e => .residual (f.residual e)

@[simp] theorem mapAnswer_realized
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F)
    (x : S.Candidate)
    (hx : S.accepts x) :
    mapAnswer f (.realized x hx) =
      (.realized (f.specification.map x)
        (f.specification.preserves x hx) : ResolutionAnswerWith T F) := by
  rfl

@[simp] theorem mapAnswer_residual
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F)
    (e : E) :
    mapAnswer f (.residual e) =
      (.residual (f.residual e) : ResolutionAnswerWith T F) := by
  rfl

/-- Unified transport is conservative on ordinary solutions. -/
@[simp] theorem mapAnswer_realize
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F)
    (x : Specification.Solution S) :
    mapAnswer f
        (ResolutionAnswerWith.realize x : ResolutionAnswerWith S E) =
      (ResolutionAnswerWith.realize
        (SpecMorphism.mapSolution f.specification x) :
          ResolutionAnswerWith T F) := by
  cases x
  rfl

/-- Unified semantic transport respects identities. -/
@[simp] theorem mapAnswer_id
    (S : Specification.{u})
    (E : Type r)
    (a : ResolutionAnswerWith S E) :
    mapAnswer (id S E) a = a := by
  cases a <;> rfl

/-- Unified semantic transport respects composition. -/
@[simp] theorem mapAnswer_comp
    {S T U : Specification.{u}}
    {E : Type r} {F : Type s} {G : Type t}
    (g : SemanticsMorphism T U F G)
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    mapAnswer (comp g f) a = mapAnswer g (mapAnswer f a) := by
  cases a <;> rfl

end SemanticsMorphism

/-! ## The two transport axes separately -/

/-- Change only the mathematical specification, retaining exactly the same
residual vocabulary. -/
def mapSpecificationWith
    {S T : Specification.{u}}
    {E : Type r}
    (f : SpecMorphism S T) :
    ResolutionAnswerWith S E -> ResolutionAnswerWith T E :=
  SemanticsMorphism.mapAnswer {
    specification := f
    residual := ResidualRefinement.id E
  }

@[simp] theorem mapSpecificationWith_realized
    {S T : Specification.{u}}
    {E : Type r}
    (f : SpecMorphism S T)
    (x : S.Candidate)
    (hx : S.accepts x) :
    mapSpecificationWith f (.realized x hx) =
      (.realized (f.map x) (f.preserves x hx) : ResolutionAnswerWith T E) := by
  rfl

@[simp] theorem mapSpecificationWith_residual
    {S T : Specification.{u}}
    {E : Type r}
    (f : SpecMorphism S T)
    (e : E) :
    mapSpecificationWith f (.residual e) =
      (.residual e : ResolutionAnswerWith T E) := by
  rfl

/-- Specification transport and residual transport commute strictly. -/
theorem specification_residual_transport_commute
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SpecMorphism S T)
    (q : ResidualRefinement E F)
    (a : ResolutionAnswerWith S E) :
    mapSpecificationWith f (ResolutionAnswerWith.mapResidual q a) =
      ResolutionAnswerWith.mapResidual q (mapSpecificationWith f a) := by
  cases a <;> rfl

/-- A unified semantic morphism may equivalently be applied by first changing
specification and then changing residual vocabulary. -/
theorem mapAnswer_eq_residual_after_specification
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    SemanticsMorphism.mapAnswer f a =
      ResolutionAnswerWith.mapResidual f.residual
        (mapSpecificationWith f.specification a) := by
  cases a <;> rfl

/-- Or equivalently by first translating residual information and then the
mathematical specification. -/
theorem mapAnswer_eq_specification_after_residual
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    SemanticsMorphism.mapAnswer f a =
      mapSpecificationWith f.specification
        (ResolutionAnswerWith.mapResidual f.residual a) := by
  cases a <;> rfl

/-! ## Naturality of the minimal semantics -/

/-- Any specification translation has a canonical semantic translation from an
arbitrary residual vocabulary to the minimal one-point residual vocabulary. -/
def toMinimalSemantics
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (E : Type r) : SemanticsMorphism S T E Unit where
  specification := f
  residual := ResidualRefinement.toUnit E

/-- Forgetting all residual provenance is natural under arbitrary translations
of mathematical specifications.  The square between structured semantics and
the original minimal `ResolutionAnswer` semantics commutes exactly. -/
theorem coarsenResidual_natural
    {S T : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : SemanticsMorphism S T E F)
    (a : ResolutionAnswerWith S E) :
    coarsenResidual (SemanticsMorphism.mapAnswer f a) =
      ResolutionAnswer.map f.specification (coarsenResidual a) := by
  cases a <;> rfl

/-- In particular, canonical transport directly into minimal semantics agrees
with first forgetting provenance and then using the already-established
minimal specification functoriality. -/
theorem toMinimalSemantics_commutes
    {S T : Specification.{u}}
    {E : Type r}
    (f : SpecMorphism S T)
    (a : ResolutionAnswerWith S E) :
    unitResidualEquiv T
        (SemanticsMorphism.mapAnswer (toMinimalSemantics f E) a) =
      ResolutionAnswer.map f (coarsenResidual a) := by
  cases a <;> rfl

/-- The action on answers of a semantic translation into the one-point
residual vocabulary is independent of how its residual function is written:
there is only one possible residual action. -/
theorem minimalResidualAction_unique
    {S T : Specification.{u}}
    {E : Type r}
    (f : SpecMorphism S T)
    (q : ResidualRefinement E Unit) :
    SemanticsMorphism.mapAnswer
        ({ specification := f, residual := q } :
          SemanticsMorphism S T E Unit) =
      SemanticsMorphism.mapAnswer (toMinimalSemantics f E) := by
  funext a
  cases a with
  | realized x hx => rfl
  | residual e =>
      have h : q e = ResidualRefinement.toUnit E e :=
        Subsingleton.elim _ _
      rw [h]

/-- For a fixed specification translation, the induced map to minimal Strong
Totality semantics is therefore canonical. -/
theorem minimalSemanticTransport_canonical
    {S T : Specification.{u}}
    {E : Type r}
    (f : SpecMorphism S T)
    (g : SemanticsMorphism S T E Unit)
    (hg : g.specification = f) :
    SemanticsMorphism.mapAnswer g =
      SemanticsMorphism.mapAnswer (toMinimalSemantics f E) := by
  cases g with
  | mk specification residual =>
      cases hg
      exact minimalResidualAction_unique f residual

end StrongTotality
end Resolution
