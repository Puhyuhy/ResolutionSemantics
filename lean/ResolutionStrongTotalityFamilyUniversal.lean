import ResolutionStrongTotalityMinimality

/-!
# Family-level universal Strong Totality

Strong Totality is fundamentally a statement about arbitrary mathematical
specifications, not about one chosen specification in isolation.  This module
packages the free-pointed universal property simultaneously over an arbitrary
dependent family `F : I -> Specification`.

A family totalization consists of one carrier, solution inclusion, and residual
point for every index.  It is universal when every family of interpretations of
those generators extends by one unique dependent family of maps.  The canonical
family `i ↦ ResolutionAnswer (F i)` satisfies this global universal property.

Crucially, the theorem is not obtained by choosing one existential witness at
each index.  The universal property quantifies over and produces the whole
family of maps at once.  Consequently every globally universal family is
structurally equivalent to the canonical Resolution family by one family of
equivalences, and that structural family equivalence is unique.
-/

universe u v

namespace Resolution
namespace StrongTotality

/-- A universal pointed totalization for an entire family of specifications.
The extension and its uniqueness are asserted simultaneously at all indices. -/
def IsUniversalTotalizationFamily
    {I : Type v}
    (F : I -> Specification.{u})
    (X : I -> Type u)
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (residual : (i : I) -> X i) : Prop :=
  forall (Y : I -> Type u)
      (onSolution :
        (i : I) -> Specification.Solution (F i) -> Y i)
      (onResidual : (i : I) -> Y i),
    Exists fun f : (i : I) -> X i -> Y i =>
      ((forall (i : I) (x : Specification.Solution (F i)),
          f i (includeSolution i x) = onSolution i x) ∧
        (forall i : I, f i (residual i) = onResidual i)) ∧
      forall g : (i : I) -> X i -> Y i,
        ((forall (i : I) (x : Specification.Solution (F i)),
            g i (includeSolution i x) = onSolution i x) ∧
          (forall i : I, g i (residual i) = onResidual i)) ->
        g = f

/-- The canonical Resolution family is globally universal.  The witness is the
whole dependent family of folds, not an index-by-index choice of witnesses. -/
theorem resolutionAnswerFamily_isUniversalTotalization
    {I : Type v}
    (F : I -> Specification.{u}) :
    IsUniversalTotalizationFamily F
      (fun i => ResolutionAnswer (F i))
      (fun i => @realizeSolution (F i))
      (fun i => (ResolutionAnswer.residual : ResolutionAnswer (F i))) := by
  intro Y onSolution onResidual
  let f : (i : I) -> ResolutionAnswer (F i) -> Y i :=
    fun i => ResolutionAnswer.fold (onSolution i) (onResidual i)
  refine ⟨f, ?_, ?_⟩
  · constructor
    · intro i x
      cases x
      rfl
    · intro i
      rfl
  · intro g hg
    funext i a
    cases a with
    | realized x hx =>
        have h := hg.1 i
          (⟨x, hx⟩ : Specification.Solution (F i))
        change g i (.realized x hx) = onSolution i ⟨x, hx⟩ at h
        change g i (.realized x hx) = onSolution i ⟨x, hx⟩
        exact h
    | residual =>
        have h := hg.2 i
        change g i
          (ResolutionAnswer.residual : ResolutionAnswer (F i)) =
            onResidual i at h
        change g i
          (ResolutionAnswer.residual : ResolutionAnswer (F i)) =
            onResidual i
        exact h

/-- Global Strong Totality for arbitrary specification families. -/
theorem strongTotality_family
    {I : Type v}
    (F : I -> Specification.{u}) :
    forall i : I, Nonempty (ResolutionAnswer (F i)) := by
  intro i
  exact strongTotality (F i)

/-- Family-level extension theorem: every interpretation of all ordinary
solutions and residual points extends by one unique dependent family of maps. -/
theorem resolutionAnswerFamily_extension_unique
    {I : Type v}
    (F : I -> Specification.{u})
    (Y : I -> Type u)
    (onSolution :
      (i : I) -> Specification.Solution (F i) -> Y i)
    (onResidual : (i : I) -> Y i) :
    Exists fun f : (i : I) -> ResolutionAnswer (F i) -> Y i =>
      ((forall (i : I) (x : Specification.Solution (F i)),
          f i (realizeSolution x) = onSolution i x) ∧
        (forall i : I,
          f i (ResolutionAnswer.residual : ResolutionAnswer (F i)) =
            onResidual i)) ∧
      forall g : (i : I) -> ResolutionAnswer (F i) -> Y i,
        ((forall (i : I) (x : Specification.Solution (F i)),
            g i (realizeSolution x) = onSolution i x) ∧
          (forall i : I,
            g i (ResolutionAnswer.residual : ResolutionAnswer (F i)) =
              onResidual i)) ->
        g = f := by
  exact resolutionAnswerFamily_isUniversalTotalization F
    Y onSolution onResidual

/-- Global structural canonicity.  Any family satisfying the simultaneous
universal property has one and only one family of equivalences to the canonical
Resolution family that preserves every ordinary solution and every residual
point. -/
theorem universalTotalizationFamily_unique_structural_equiv
    {I : Type v}
    (F : I -> Specification.{u})
    (X : I -> Type u)
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (residual : (i : I) -> X i)
    (hX : IsUniversalTotalizationFamily F X includeSolution residual) :
    Exists fun e : (i : I) -> Equiv (X i) (ResolutionAnswer (F i)) =>
      ((forall (i : I) (x : Specification.Solution (F i)),
          e i (includeSolution i x) = realizeSolution x) ∧
        (forall i : I,
          e i (residual i) =
            (ResolutionAnswer.residual : ResolutionAnswer (F i)))) ∧
      forall g : (i : I) -> Equiv (X i) (ResolutionAnswer (F i)),
        ((forall (i : I) (x : Specification.Solution (F i)),
            g i (includeSolution i x) = realizeSolution x) ∧
          (forall i : I,
            g i (residual i) =
              (ResolutionAnswer.residual : ResolutionAnswer (F i)))) ->
        g = e := by
  rcases hX
      (fun i => ResolutionAnswer (F i))
      (fun i => @realizeSolution (F i))
      (fun i => (ResolutionAnswer.residual : ResolutionAnswer (F i))) with
    ⟨toRA, hto, htoUnique⟩
  rcases resolutionAnswerFamily_isUniversalTotalization F
      X includeSolution residual with
    ⟨fromRA, hfrom, _⟩
  have hleftFamily :
      (fun (i : I) (z : X i) => fromRA i (toRA i z)) =
        (fun (i : I) (z : X i) => z) := by
    have hcompPreserves :
        ((forall (i : I) (x : Specification.Solution (F i)),
            fromRA i (toRA i (includeSolution i x)) =
              includeSolution i x) ∧
          (forall i : I,
            fromRA i (toRA i (residual i)) = residual i)) := by
      constructor
      · intro i x
        calc
          fromRA i (toRA i (includeSolution i x)) =
              fromRA i (realizeSolution x) :=
            congrArg (fromRA i) (hto.1 i x)
          _ = includeSolution i x := hfrom.1 i x
      · intro i
        calc
          fromRA i (toRA i (residual i)) =
              fromRA i
                (ResolutionAnswer.residual : ResolutionAnswer (F i)) :=
            congrArg (fromRA i) (hto.2 i)
          _ = residual i := hfrom.2 i
    have hidPreserves :
        ((forall (i : I) (x : Specification.Solution (F i)),
            (fun z : X i => z) (includeSolution i x) =
              includeSolution i x) ∧
          (forall i : I,
            (fun z : X i => z) (residual i) = residual i)) := by
      exact ⟨fun _ _ => rfl, fun _ => rfl⟩
    rcases hX X includeSolution residual with ⟨k, _, huniq⟩
    have hc :
        (fun (i : I) (z : X i) => fromRA i (toRA i z)) = k :=
      huniq _ hcompPreserves
    have hi : (fun (i : I) (z : X i) => z) = k :=
      huniq _ hidPreserves
    exact hc.trans hi.symm
  let e : (i : I) -> Equiv (X i) (ResolutionAnswer (F i)) :=
    fun i => {
      toFun := toRA i
      invFun := fromRA i
      left_inv := by
        intro x
        exact congrArg (fun k => k i x) hleftFamily
      right_inv := by
        intro a
        cases a with
        | realized x hx =>
            let sx : Specification.Solution (F i) := ⟨x, hx⟩
            calc
              toRA i (fromRA i (.realized x hx)) =
                  toRA i (fromRA i (realizeSolution sx)) := by rfl
              _ = toRA i (includeSolution i sx) :=
                congrArg (toRA i) (hfrom.1 i sx)
              _ = realizeSolution sx := hto.1 i sx
              _ = .realized x hx := by rfl
        | residual =>
            calc
              toRA i (fromRA i
                  (ResolutionAnswer.residual : ResolutionAnswer (F i))) =
                  toRA i (residual i) :=
                congrArg (toRA i) (hfrom.2 i)
              _ = (ResolutionAnswer.residual : ResolutionAnswer (F i)) :=
                hto.2 i
    }
  refine ⟨e, ?_, ?_⟩
  · constructor
    · intro i x
      change toRA i (includeSolution i x) = realizeSolution x
      exact hto.1 i x
    · intro i
      change toRA i (residual i) =
        (ResolutionAnswer.residual : ResolutionAnswer (F i))
      exact hto.2 i
  · intro g hg
    have hgFun :
        (fun (i : I) (x : X i) => g i x) = toRA := by
      exact htoUnique (fun i x => g i x) hg
    funext i
    apply Equiv.ext
    funext x
    exact congrArg (fun k => k i x) hgFun

end StrongTotality
end Resolution
