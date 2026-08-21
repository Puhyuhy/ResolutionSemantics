import ResolutionStrongTotalityResidualStructure

/-!
# Canonical semantic obstructions and the classical boundary

The minimal Strong Totality completion uses a single residual point.  This is
constructively total because the residual means only that no ordinary solution
has been supplied.  A stronger interpretation would demand that a residual
carry an actual proof that the specification has no ordinary solution.

This module isolates that stronger semantics.  The canonical semantic
obstruction of `S` is a proof-carrying type whose inhabitant certifies
`¬ Satisfiable S`.  Structured Resolution Answers with this residual vocabulary
are constructively equivalent to the already-defined `DecisiveResolutionAnswer`.

The key result identifies the exact logical price of making these semantic
obstructions uniformly total: over universe-zero specifications it is
*equivalent to propositional excluded middle*.  Thus the unconditional
constructive residual of Strong Totality and a proof of impossibility are
mathematically distinct notions, and the distinction is necessary rather than
merely stylistic.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- A canonical semantic residual for `S`: not merely an unresolved marker,
but a certificate that no ordinary satisfying candidate exists. -/
structure SemanticObstruction (S : Specification.{u}) : Type where
  impossible : Not (Specification.Satisfiable S)

/-- Resolution semantics whose residual branch carries a genuine semantic
obstruction certificate. -/
abbrev ObstructionResolutionAnswer (S : Specification.{u}) : Type u :=
  ResolutionAnswerWith S (SemanticObstruction S)

/-- The semantic obstruction type is inhabited exactly when the specification
is ordinarily unsatisfiable. -/
theorem semanticObstruction_nonempty_iff
    (S : Specification.{u}) :
    Nonempty (SemanticObstruction S) ↔
      Not (Specification.Satisfiable S) := by
  constructor
  · intro h
    rcases h with ⟨o⟩
    exact o.impossible
  · intro h
    exact ⟨⟨h⟩⟩

/-- A genuine ordinary solution and a semantic obstruction cannot coexist. -/
theorem solution_excludes_semanticObstruction
    {S : Specification.{u}}
    (x : Specification.Solution S)
    (o : SemanticObstruction S) : False := by
  exact o.impossible ⟨x.1, x.2⟩

/-- The older decisive answer presentation is exactly the structured Resolution
presentation whose residual provenance is a semantic obstruction proof. -/
def decisiveResolutionEquivObstruction
    (S : Specification.{u}) :
    Equiv (DecisiveResolutionAnswer S) (ObstructionResolutionAnswer S) where
  toFun := fun a =>
    match a with
    | .realized x hx => .realized x hx
    | .impossible h => .residual ⟨h⟩
  invFun := fun a =>
    match a with
    | .realized x hx => .realized x hx
    | .residual o => .impossible o.impossible
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro a
    cases a <;> rfl

/-- A proof-carrying obstruction answer exists exactly when satisfiability is
decided for this specification. -/
theorem obstructionResolution_nonempty_iff
    (S : Specification.{u}) :
    Nonempty (ObstructionResolutionAnswer S) ↔
      Specification.Satisfiable S ∨
        Not (Specification.Satisfiable S) := by
  constructor
  · intro h
    have hor :=
      (resolutionAnswerWith_nonempty_iff S (SemanticObstruction S)).1 h
    cases hor with
    | inl hs =>
        exact Or.inl hs
    | inr ho =>
        exact Or.inr ((semanticObstruction_nonempty_iff S).1 ho)
  · intro h
    apply (resolutionAnswerWith_nonempty_iff S (SemanticObstruction S)).2
    cases h with
    | inl hs =>
        exact Or.inl hs
    | inr hns =>
        exact Or.inr ((semanticObstruction_nonempty_iff S).2 hns)

/-- For proposition specifications, ordinary satisfiability is exactly truth of
the proposition itself. -/
theorem propositionSpecification_satisfiable_iff
    (P : Prop) :
    Specification.Satisfiable (propositionSpecification P) ↔ P := by
  constructor
  · intro h
    rcases h with ⟨_, hP⟩
    exact hP
  · intro hP
    exact ⟨(), hP⟩

/-- **Classical-boundary theorem.**  Uniform totality of Resolution semantics
whose residuals are actual impossibility certificates is equivalent to full
propositional excluded middle. -/
theorem uniformObstructionResolution_iff_excludedMiddle :
    (forall S : Specification.{0},
      Nonempty (ObstructionResolutionAnswer S)) ↔
    (forall P : Prop, P ∨ Not P) := by
  constructor
  · intro hTotal P
    have hDecision :=
      (obstructionResolution_nonempty_iff
        (propositionSpecification P)).1
        (hTotal (propositionSpecification P))
    cases hDecision with
    | inl hs =>
        exact Or.inl
          ((propositionSpecification_satisfiable_iff P).1 hs)
    | inr hns =>
        apply Or.inr
        intro hP
        exact hns
          ((propositionSpecification_satisfiable_iff P).2 hP)
  · intro hEM S
    exact (obstructionResolution_nonempty_iff S).2
      (hEM (Specification.Satisfiable S))

/-- The same boundary applies to the original decisive-answer presentation.
The classical theorem `decisiveStrongTotality` is therefore not merely one
possible proof technique: uniform decisiveness has exactly excluded-middle
strength. -/
theorem uniformDecisiveStrongTotality_iff_excludedMiddle :
    (forall S : Specification.{0},
      Nonempty (DecisiveResolutionAnswer S)) ↔
    (forall P : Prop, P ∨ Not P) := by
  constructor
  · intro hDecisive
    apply (uniformObstructionResolution_iff_excludedMiddle).1
    intro S
    rcases hDecisive S with ⟨a⟩
    exact ⟨decisiveResolutionEquivObstruction S a⟩
  · intro hEM
    have hObstruction :=
      (uniformObstructionResolution_iff_excludedMiddle).2 hEM
    intro S
    rcases hObstruction S with ⟨a⟩
    exact ⟨(decisiveResolutionEquivObstruction S).symm a⟩

/-- Constructive Strong Totality needs no such logical principle: the minimal
one-point residual semantics remains uniformly inhabited without deciding
satisfiability. -/
theorem minimalStrongTotality_uniform_constructive :
    forall S : Specification.{0}, Nonempty (ResolutionAnswer S) := by
  intro S
  exact strongTotality S

end StrongTotality
end Resolution
