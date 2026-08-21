import ResolutionStrongTotalityResidualStructure

/-!
# Canonical normal forms for Strong Totality

The Resolution completion contains no hidden semantic states.  For an ordinary
specification `S`, its answer type is exactly the disjoint sum of the ordinary
solution space and one residual point:

  `ResolutionAnswer S ≃ Specification.Solution S ⊕ Unit`.

The structured-residual construction is the corresponding general form:

  `ResolutionAnswerWith S E ≃ Specification.Solution S ⊕ E`.

These equivalences make the minimal shape of Strong Totality explicit.  The
construction preserves every ordinary solution and adds exactly the chosen
residual vocabulary, nothing more.
-/

universe u r

namespace Resolution
namespace StrongTotality

/-- Canonical sum normal form for the one-residual Resolution completion. -/
def resolutionAnswerEquivSum
    (S : Specification.{u}) :
    Equiv (ResolutionAnswer S) (Sum (Specification.Solution S) Unit) where
  toFun := fun a =>
    match a with
    | .realized x hx => .inl ⟨x, hx⟩
    | .residual => .inr ()
  invFun := fun z =>
    match z with
    | .inl x => realizeSolution x
    | .inr _ => .residual
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro z
    cases z with
    | inl x =>
        cases x
        rfl
    | inr e =>
        cases e
        rfl

/-- Under the canonical normal form, an ordinary solution is exactly the left
summand. -/
theorem resolutionAnswerEquivSum_realizeSolution
    (S : Specification.{u})
    (x : Specification.Solution S) :
    resolutionAnswerEquivSum S (realizeSolution x) = Sum.inl x := by
  cases x
  rfl

/-- Under the canonical normal form, the unique residual answer is exactly the
single point in the right summand. -/
theorem resolutionAnswerEquivSum_residual
    (S : Specification.{u}) :
    resolutionAnswerEquivSum S
        (ResolutionAnswer.residual : ResolutionAnswer S) =
      Sum.inr () := by
  rfl

/-- The structured residual normal form is the already canonical sum
presentation: ordinary solutions occupy the left summand and residual
provenance occupies the right summand. -/
def structuredResolutionAnswerEquivSum
    (S : Specification.{u})
    (E : Type r) :
    Equiv (ResolutionAnswerWith S E)
      (Sum (Specification.Solution S) E) :=
  ResolutionAnswerWith.equivSum S E

/-- Structured ordinary solutions are exactly the left summand of the normal
form. -/
theorem structuredResolutionAnswerEquivSum_realize
    (S : Specification.{u})
    (E : Type r)
    (x : Specification.Solution S) :
    structuredResolutionAnswerEquivSum S E
        (ResolutionAnswerWith.realize x) =
      Sum.inl x := by
  cases x
  rfl

/-- Structured residual provenance is exactly the right summand of the normal
form. -/
theorem structuredResolutionAnswerEquivSum_residual
    (S : Specification.{u})
    (E : Type r)
    (e : E) :
    structuredResolutionAnswerEquivSum S E
        (ResolutionAnswerWith.residual e) =
      Sum.inr e := by
  rfl

/-- The one-residual theory is the `E = Unit` instance of the structured normal
form, so the minimal Strong Totality completion literally adds one point. -/
theorem resolutionAnswer_is_solution_plus_one
    (S : Specification.{u}) :
    Nonempty
      (Equiv (ResolutionAnswer S)
        (Sum (Specification.Solution S) Unit)) := by
  exact ⟨resolutionAnswerEquivSum S⟩

end StrongTotality
end Resolution
