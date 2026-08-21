import ResolutionStrongTotalityFamilyUniversal

/-!
# Single specifications as singleton Strong Totality families

The family-level theory is a genuine generalization of the original
single-specification theory, not a parallel construction.  This module proves
that a pointed completion of one specification is universal exactly when the
corresponding constant family indexed by `Unit` is universally totalizing.

Consequently the original universal Strong Totality theorem can be recovered
from the family theorem by specializing the index type to `Unit`.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- The singleton family associated to one specification. -/
def singletonSpecificationFamily
    (S : Specification.{u}) : Unit -> Specification.{u} :=
  fun _ => S

/-- Single-specification universality is exactly family universality for the
constant family indexed by `Unit`. -/
theorem isUniversalTotalization_iff_singletonFamily
    (S : Specification.{u})
    (X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (residual : X) :
    IsUniversalTotalization S X includeSolution residual ↔
      IsUniversalTotalizationFamily
        (singletonSpecificationFamily S)
        (fun _ : Unit => X)
        (fun _ => includeSolution)
        (fun _ => residual) := by
  constructor
  · intro hSingle
    intro Y onSolution onResidual
    rcases hSingle (Y ()) (onSolution ()) (onResidual ()) with
      ⟨f0, hf0, hUnique0⟩
    let f : (i : Unit) -> X -> Y i := fun i =>
      match i with
      | () => f0
    refine ⟨f, ?_, ?_⟩
    · constructor
      · intro i x
        cases i
        exact hf0.1 x
      · intro i
        cases i
        exact hf0.2
    · intro g hg
      have hg0Preserves :
          ((forall x : Specification.Solution S,
              g () (includeSolution x) = onSolution () x) ∧
            g () residual = onResidual ()) := by
        exact ⟨fun x => hg.1 () x, hg.2 ()⟩
      have hg0 : g () = f0 := hUnique0 (g ()) hg0Preserves
      funext i x
      cases i
      exact congrArg (fun q => q x) hg0
  · intro hFamily
    intro Y onSolution onResidual
    rcases hFamily
        (fun _ : Unit => Y)
        (fun _ => onSolution)
        (fun _ => onResidual) with
      ⟨f, hf, hUnique⟩
    refine ⟨f (), ?_, ?_⟩
    · exact ⟨fun x => hf.1 () x, hf.2 ()⟩
    · intro g hg
      let gFamily : (i : Unit) -> X -> Y := fun _ => g
      have hgFamilyPreserves :
          ((forall (i : Unit)
              (x : Specification.Solution (singletonSpecificationFamily S i)),
              gFamily i ((fun _ => includeSolution) i x) =
                (fun _ => onSolution) i x) ∧
            (forall i : Unit,
              gFamily i ((fun _ => residual) i) =
                (fun _ => onResidual) i)) := by
        constructor
        · intro i x
          cases i
          exact hg.1 x
        · intro i
          cases i
          exact hg.2
      have hgf : gFamily = f := hUnique gFamily hgFamilyPreserves
      calc
        g = gFamily () := by rfl
        _ = f () := congrArg (fun k => k ()) hgf

/-- The original canonical universal theorem is derivable from the family-level
universal theorem by specializing to the singleton index type. -/
theorem resolutionAnswer_universal_from_singletonFamily
    (S : Specification.{u}) :
    IsUniversalTotalization S (ResolutionAnswer S)
      (@realizeSolution S)
      (ResolutionAnswer.residual : ResolutionAnswer S) := by
  apply (isUniversalTotalization_iff_singletonFamily
    S (ResolutionAnswer S) (@realizeSolution S)
      (ResolutionAnswer.residual : ResolutionAnswer S)).2
  exact resolutionAnswerFamily_isUniversalTotalization
    (singletonSpecificationFamily S)

/-- Conversely, the singleton instance of family universality follows directly
from the original single-specification universal theorem. -/
theorem resolutionAnswer_singletonFamily_from_universal
    (S : Specification.{u}) :
    IsUniversalTotalizationFamily
      (singletonSpecificationFamily S)
      (fun _ : Unit => ResolutionAnswer S)
      (fun _ => @realizeSolution S)
      (fun _ => (ResolutionAnswer.residual : ResolutionAnswer S)) := by
  apply (isUniversalTotalization_iff_singletonFamily
    S (ResolutionAnswer S) (@realizeSolution S)
      (ResolutionAnswer.residual : ResolutionAnswer S)).1
  exact resolutionAnswer_isUniversalTotalization S

end StrongTotality
end Resolution
