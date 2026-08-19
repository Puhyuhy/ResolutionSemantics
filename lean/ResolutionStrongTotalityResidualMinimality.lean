import ResolutionStrongTotalityResidualStructure

/-!
# Minimal residual vocabulary for Strong Totality

`ResolutionAnswerWith S E` separates ordinary satisfying solutions from a
chosen residual vocabulary `E`.  This module gives the exact inhabitation
criterion and derives the sharp minimality statement behind uniform Strong
Totality.

For a fixed specification, a structured Resolution Answer exists exactly when
there is either an ordinary satisfying solution or at least one residual value.
Consequently, on every unsatisfiable specification, inhabitation of the answer
space is equivalent to inhabitation of the residual vocabulary itself.

The same criterion is forced on every universal residual extension, not merely
on the canonical constructor.  Hence a universal competitor cannot obtain a
nonempty total semantics for an unsatisfiable specification while using an
empty residual vocabulary.

Thus one residual point is not merely sufficient for unconditional totality.
In the presence of any unsatisfiable specification it is also necessary.  The
canonical `Unit` residual therefore has the smallest possible nonempty shape
for a uniform total completion.
-/

universe u r

namespace Resolution
namespace StrongTotality

/-- Exact inhabitation criterion for a structured Resolution Answer. -/
theorem resolutionAnswerWith_nonempty_iff
    (S : Specification.{u})
    (E : Type r) :
    Nonempty (ResolutionAnswerWith S E) ↔
      Specification.Satisfiable S ∨ Nonempty E := by
  constructor
  · intro h
    rcases h with ⟨a⟩
    cases a with
    | realized x hx =>
        exact Or.inl ⟨x, hx⟩
    | residual e =>
        exact Or.inr ⟨e⟩
  · intro h
    cases h with
    | inl hs =>
        rcases hs with ⟨x, hx⟩
        exact ⟨.realized x hx⟩
    | inr he =>
        rcases he with ⟨e⟩
        exact ⟨.residual e⟩

/-- Every universal residual extension has exactly the same inhabitation
criterion as the canonical structured answer space.  In particular,
universality itself prevents hidden states from making an otherwise empty
completion nonempty. -/
theorem universalResidualExtension_nonempty_iff
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Nonempty X ↔ Specification.Satisfiable S ∨ Nonempty E := by
  constructor
  · intro h
    rcases h with ⟨z⟩
    rcases hX
        (ResolutionAnswerWith S E)
        (@ResolutionAnswerWith.realize S E)
        (fun e : E =>
          (ResolutionAnswerWith.residual e : ResolutionAnswerWith S E)) with
      ⟨toCanonical, _, _⟩
    cases toCanonical z with
    | realized x hx =>
        exact Or.inl ⟨x, hx⟩
    | residual e =>
        exact Or.inr ⟨e⟩
  · intro h
    cases h with
    | inl hs =>
        rcases hs with ⟨x, hx⟩
        exact ⟨includeSolution ⟨x, hx⟩⟩
    | inr he =>
        rcases he with ⟨e⟩
        exact ⟨includeResidual e⟩

/-- A universal residual extension and the canonical structured answer space
are inhabited under exactly the same circumstances. -/
theorem universalResidualExtension_nonempty_iff_canonical
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual) :
    Nonempty X ↔ Nonempty (ResolutionAnswerWith S E) := by
  exact (universalResidualExtension_nonempty_iff
    S E X includeSolution includeResidual hX).trans
      (resolutionAnswerWith_nonempty_iff S E).symm

/-- On an unsatisfiable specification, a structured Resolution Answer exists
exactly when the residual vocabulary itself has an inhabitant. -/
theorem unsatisfiable_resolutionAnswerWith_nonempty_iff
    (S : Specification.{u})
    (E : Type r)
    (hS : Not (Specification.Satisfiable S)) :
    Nonempty (ResolutionAnswerWith S E) ↔ Nonempty E := by
  constructor
  · intro h
    have hcases := (resolutionAnswerWith_nonempty_iff S E).1 h
    cases hcases with
    | inl hs =>
        exact False.elim (hS hs)
    | inr he =>
        exact he
  · intro he
    exact (resolutionAnswerWith_nonempty_iff S E).2 (Or.inr he)

/-- The no-go form of residual minimality: for an unsatisfiable specification,
every universal residual extension is nonempty exactly when its residual
vocabulary is nonempty. -/
theorem unsatisfiable_universalResidualExtension_nonempty_iff
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual)
    (hS : Not (Specification.Satisfiable S)) :
    Nonempty X ↔ Nonempty E := by
  constructor
  · intro h
    have hcases := (universalResidualExtension_nonempty_iff
      S E X includeSolution includeResidual hX).1 h
    cases hcases with
    | inl hs =>
        exact False.elim (hS hs)
    | inr he =>
        exact he
  · intro he
    exact (universalResidualExtension_nonempty_iff
      S E X includeSolution includeResidual hX).2 (Or.inr he)

/-- Any inhabited universal total semantics for an unsatisfiable specification
therefore forces the residual vocabulary itself to be inhabited. -/
theorem unsatisfiable_universalResidualExtension_requires_residual
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X)
    (hX : IsUniversalResidualExtension S E X includeSolution includeResidual)
    (hS : Not (Specification.Satisfiable S))
    (hNonempty : Nonempty X) :
    Nonempty E :=
  (unsatisfiable_universalResidualExtension_nonempty_iff
    S E X includeSolution includeResidual hX hS).1 hNonempty

/-- Any inhabited residual vocabulary is sufficient to totalize every
specification, independently of whether that specification is satisfiable. -/
theorem residual_inhabited_sufficient_for_all
    (E : Type r)
    (hE : Nonempty E) :
    forall S : Specification.{u}, Nonempty (ResolutionAnswerWith S E) := by
  intro S
  rcases hE with ⟨e⟩
  exact strongTotalityWith S e

/-- If the universe contains one unsatisfiable specification, then a residual
vocabulary supports Strong Totality uniformly for all specifications exactly
when that residual vocabulary is inhabited. -/
theorem residual_inhabited_iff_uniformStrongTotality
    (S0 : Specification.{u})
    (hS0 : Not (Specification.Satisfiable S0))
    (E : Type r) :
    Nonempty E ↔
      forall S : Specification.{u}, Nonempty (ResolutionAnswerWith S E) := by
  constructor
  · intro hE
    exact residual_inhabited_sufficient_for_all E hE
  · intro hall
    exact (unsatisfiable_resolutionAnswerWith_nonempty_iff S0 E hS0).1
      (hall S0)

/-- The one-point residual vocabulary is uniformly sufficient.  Together with
`residual_inhabited_iff_uniformStrongTotality`, this records the literal
minimality of the canonical fallback shape: no empty residual vocabulary can
provide uniform totality in the presence of an unsatisfiable specification. -/
theorem unitResidual_uniformStrongTotality
    (S : Specification.{u}) :
    Nonempty (ResolutionAnswerWith S Unit) := by
  exact strongTotalityWith S ()

end StrongTotality
end Resolution
