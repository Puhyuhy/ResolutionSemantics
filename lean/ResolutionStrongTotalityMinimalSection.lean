import ResolutionStrongTotalityFibration

/-!
# The canonical minimal section

The split projection from structured Strong Totality semantics to mathematical
specifications has a canonical section: send every specification `S` to the
minimal one-residual semantic object `(S, Unit)`, and every specification
morphism to the same base morphism together with the unique residual map on
`Unit`.

The projection of this section is exactly the identity on specifications.  On
Resolution Answers, this section recovers the original minimal
`ResolutionAnswer` functor after the canonical `Unit`-residual equivalence.

Finally, the unique fiberwise coarsening from any structured semantics to its
minimal object is natural with respect to arbitrary total semantic morphisms.
This packages the earlier terminality and naturality results into one global
coherent picture.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- The minimal semantic object selected over each specification. -/
def minimalSectionObject
    (S : Specification.{u}) : TotalSemanticsObject :=
  TotalSemanticsObject.minimal S

/-- The minimal section sends a specification morphism to the same base map and
the identity map on the one-point residual vocabulary. -/
def minimalSectionMap
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    TotalSemanticsHom (minimalSectionObject S) (minimalSectionObject T) where
  specification := f
  residual := ResidualRefinement.id Unit

/-- The section is literally a section of the projection on objects. -/
@[simp] theorem minimalSection_projection_object
    (S : Specification.{u}) :
    semanticsProjection (minimalSectionObject S) = S := by
  rfl

/-- The section is literally a section of the projection on morphisms. -/
@[simp] theorem minimalSection_projection_map
    {S T : Specification.{u}}
    (f : SpecMorphism S T) :
    semanticsProjectionMap (minimalSectionMap f) = f := by
  rfl

/-- The minimal section respects identity on Resolution Answers. -/
@[simp] theorem minimalSection_id_on_answers
    (S : Specification.{u})
    (a : ResolutionAnswerWith S Unit) :
    SemanticsMorphism.mapAnswer
        (minimalSectionMap (SpecMorphism.id S)) a = a := by
  cases a <;> rfl

/-- The minimal section respects composition on Resolution Answers. -/
theorem minimalSection_comp_on_answers
    {R S T : Specification.{u}}
    (f : SpecMorphism R S)
    (g : SpecMorphism S T)
    (a : ResolutionAnswerWith R Unit) :
    SemanticsMorphism.mapAnswer
        (minimalSectionMap (SpecMorphism.comp g f)) a =
      SemanticsMorphism.mapAnswer (minimalSectionMap g)
        (SemanticsMorphism.mapAnswer (minimalSectionMap f) a) := by
  cases a <;> rfl

/-- After identifying the one-point structured answer with the original
minimal answer type, the minimal section acts exactly by the previously defined
`ResolutionAnswer.map`. -/
theorem minimalSection_recovers_minimal_map
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (a : ResolutionAnswerWith S Unit) :
    unitResidualEquiv T
        (SemanticsMorphism.mapAnswer (minimalSectionMap f) a) =
      ResolutionAnswer.map f (unitResidualEquiv S a) := by
  cases a <;> rfl

/-! ## Canonical coarsening into the section -/

/-- Every total semantic object has a canonical vertical morphism to the
minimal section object over the same specification. -/
def objectToMinimalSection
    (A : TotalSemanticsObject.{u}) :
    TotalSemanticsHom A (minimalSectionObject A.specification) where
  specification := SpecMorphism.id A.specification
  residual := ResidualRefinement.toUnit A.Residual

/-- This canonical coarsening is vertical: its base projection is identity. -/
@[simp] theorem objectToMinimalSection_projection
    (A : TotalSemanticsObject.{u}) :
    semanticsProjectionMap (objectToMinimalSection A) =
      SpecMorphism.id A.specification := by
  rfl

/-- The canonical coarsening acts on answers exactly as provenance forgetting,
after the `Unit` residual answer is identified with the original minimal answer. -/
theorem objectToMinimalSection_on_answers
    (A : TotalSemanticsObject.{u})
    (a : ResolutionAnswerWith A.specification A.Residual) :
    unitResidualEquiv A.specification
        (SemanticsMorphism.mapAnswer (objectToMinimalSection A) a) =
      coarsenResidual a := by
  cases a <;> rfl

/-- Naturality of canonical coarsening: for every total semantic morphism
`f : A -> B`, one may either transport the structured answer and then forget
residual provenance, or first forget provenance and then transport in the
minimal section. -/
theorem objectToMinimalSection_natural_on_answers
    {A B : TotalSemanticsObject.{u}}
    (f : TotalSemanticsHom A B)
    (a : ResolutionAnswerWith A.specification A.Residual) :
    unitResidualEquiv B.specification
      (SemanticsMorphism.mapAnswer (objectToMinimalSection B)
        (SemanticsMorphism.mapAnswer f a)) =
    unitResidualEquiv B.specification
      (SemanticsMorphism.mapAnswer (minimalSectionMap f.specification)
        (SemanticsMorphism.mapAnswer (objectToMinimalSection A) a)) := by
  cases a <;> rfl

/-- Equivalent minimal-answer formulation of the naturality square. -/
theorem coarsen_to_minimalSection_natural
    {A B : TotalSemanticsObject.{u}}
    (f : TotalSemanticsHom A B)
    (a : ResolutionAnswerWith A.specification A.Residual) :
    coarsenResidual (SemanticsMorphism.mapAnswer f a) =
      ResolutionAnswer.map f.specification (coarsenResidual a) := by
  exact coarsenResidual_natural f a

/-- Fiberwise terminality says that the vertical arrow to the minimal section
is unique among residual translations over the identity base map. -/
theorem objectToMinimalSection_residual_unique
    (A : TotalSemanticsObject.{u})
    (g : TotalSemanticsHom A (minimalSectionObject A.specification))
    (hbase : g.specification = SpecMorphism.id A.specification) :
    g.residual = (objectToMinimalSection A).residual := by
  exact ResidualRefinement.toUnit_unique A.Residual g.residual

end StrongTotality
end Resolution
