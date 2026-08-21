import ResolutionStrongTotalityFreeUniversal

/-!
# Exactness of Strong Totality

The bare existence theorem for `ResolutionAnswer S` is intentionally total:
every specification has at least the residual answer.  The mathematical content
must therefore distinguish total Resolution semantics from ordinary
satisfiability exactly, rather than allowing the residual point to masquerade
as a solution.

This module proves that distinction is sharp.

* `S` is ordinarily satisfiable exactly when its Resolution completion contains
  a non-residual answer.
* `S` is ordinarily unsatisfiable exactly when every Resolution Answer is the
  residual point.
* Equivalently, an unsatisfiable specification has a subsingleton Resolution
  completion, while a satisfiable specification forces at least two distinct
  completion states: one realized solution and the residual.

Thus Strong Totality neither creates ordinary solutions nor destroys them.  It
adds exactly one canonical point beyond the ordinary solution space, and the
presence or absence of realized answers continues to detect ordinary
satisfiability without loss.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- Ordinary satisfiability is exactly the existence of a non-residual
Resolution Answer. -/
theorem satisfiable_iff_exists_nonresidual
    (S : Specification.{u}) :
    Specification.Satisfiable S ↔
      Exists fun a : ResolutionAnswer S =>
        a ≠ (ResolutionAnswer.residual : ResolutionAnswer S) := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    let sx : Specification.Solution S := ⟨x, hx⟩
    exact ⟨realizeSolution sx, realizeSolution_ne_residual sx⟩
  · intro h
    rcases h with ⟨a, ha⟩
    cases a with
    | realized x hx =>
        exact ⟨x, hx⟩
    | residual =>
        exact False.elim (ha rfl)

/-- Ordinary unsatisfiability is exactly the statement that the residual point
is the only Resolution Answer. -/
theorem not_satisfiable_iff_all_residual
    (S : Specification.{u}) :
    Not (Specification.Satisfiable S) ↔
      forall a : ResolutionAnswer S,
        a = (ResolutionAnswer.residual : ResolutionAnswer S) := by
  constructor
  · intro h a
    cases a with
    | residual => rfl
    | realized x hx =>
        exact False.elim (h ⟨x, hx⟩)
  · intro h hs
    rcases hs with ⟨x, hx⟩
    let sx : Specification.Solution S := ⟨x, hx⟩
    exact realizeSolution_ne_residual sx (h (realizeSolution sx))

/-- An unsatisfiable specification has no hidden multiplicity in its completion:
the residual is the unique answer. -/
theorem not_satisfiable_iff_resolutionAnswer_subsingleton
    (S : Specification.{u}) :
    Not (Specification.Satisfiable S) ↔ Subsingleton (ResolutionAnswer S) := by
  constructor
  · intro h
    have hall := (not_satisfiable_iff_all_residual S).1 h
    exact {
      allEq := by
        intro a b
        exact (hall a).trans (hall b).symm
    }
  · intro h hs
    rcases hs with ⟨x, hx⟩
    let sx : Specification.Solution S := ⟨x, hx⟩
    have heq :
        realizeSolution sx =
          (ResolutionAnswer.residual : ResolutionAnswer S) :=
      h.elim _ _
    exact realizeSolution_ne_residual sx heq

/-- Every ordinary solution remains visibly distinct from the residual point.
Hence satisfiability forces the completion to contain at least two distinct
answers. -/
theorem satisfiable_gives_distinct_resolutionAnswers
    (S : Specification.{u})
    (h : Specification.Satisfiable S) :
    Exists fun a : ResolutionAnswer S =>
      Exists fun b : ResolutionAnswer S => a ≠ b := by
  rcases h with ⟨x, hx⟩
  let sx : Specification.Solution S := ⟨x, hx⟩
  exact ⟨realizeSolution sx, .residual, realizeSolution_ne_residual sx⟩

/-- Exactness theorem in operational form: a Resolution Answer carries an
ordinary solution precisely when it is not the residual point. -/
theorem solution?_isSome_iff_nonresidual
    {S : Specification.{u}}
    (a : ResolutionAnswer S) :
    (Exists fun x : Specification.Solution S => a.solution? = some x) ↔
      a ≠ (ResolutionAnswer.residual : ResolutionAnswer S) := by
  cases a with
  | residual =>
      constructor
      · intro h
        rcases h with ⟨x, hx⟩
        cases hx
      · intro h
        exact False.elim (h rfl)
  | realized x hx =>
      let sx : Specification.Solution S := ⟨x, hx⟩
      constructor
      · intro _
        exact realizeSolution_ne_residual sx
      · intro _
        exact ⟨sx, rfl⟩

/-- Strong Totality is therefore conservative and exact with respect to
ordinary existence: totality of Resolution Answers is unconditional, while
non-residual totality is equivalent to ordinary satisfiability. -/
theorem strongTotality_exact
    (S : Specification.{u}) :
    Nonempty (ResolutionAnswer S) ∧
      (Specification.Satisfiable S ↔
        Exists fun a : ResolutionAnswer S =>
          a ≠ (ResolutionAnswer.residual : ResolutionAnswer S)) := by
  exact ⟨strongTotality S, satisfiable_iff_exists_nonresidual S⟩

end StrongTotality
end Resolution
