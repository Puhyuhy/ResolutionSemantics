import ResolutionStrongTotalityResidualMinimality

/-!
# Family-level structured residual provenance

Strong Totality with provenance should globalize to arbitrary dependent families
without collapsing each unresolved fiber to one undifferentiated point.  For a
family of specifications `F : I -> Specification` and a family of residual
vocabularies `E : I -> Type`, the canonical fiber is

  `ResolutionAnswerWith (F i) (E i)`.

This module gives the simultaneous dependent universal property for that
construction.  It also proves global structural canonicity and the exact
fiberwise inhabitation criterion.  Thus a universal family completion cannot
hide extra states or manufacture residual provenance absent from the chosen
vocabulary.
-/

universe u r v

namespace Resolution
namespace StrongTotality

/-- Simultaneous universal property for a family of specifications equipped
with a possibly different residual vocabulary in every fiber. -/
def IsUniversalResidualExtensionFamily
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (X : I -> Type (max u r))
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (includeResidual : (i : I) -> E i -> X i) : Prop :=
  forall (Y : I -> Type (max u r))
      (onSolution :
        (i : I) -> Specification.Solution (F i) -> Y i)
      (onResidual : (i : I) -> E i -> Y i),
    Exists fun f : (i : I) -> X i -> Y i =>
      ((forall (i : I) (x : Specification.Solution (F i)),
          f i (includeSolution i x) = onSolution i x) ∧
        (forall (i : I) (q : E i),
          f i (includeResidual i q) = onResidual i q)) ∧
      forall g : (i : I) -> X i -> Y i,
        ((forall (i : I) (x : Specification.Solution (F i)),
            g i (includeSolution i x) = onSolution i x) ∧
          (forall (i : I) (q : E i),
            g i (includeResidual i q) = onResidual i q)) ->
        g = f

/-- The canonical structured Resolution family satisfies the global dependent
universal property. -/
theorem resolutionAnswerWithFamily_isUniversalResidualExtension
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r) :
    IsUniversalResidualExtensionFamily F E
      (fun i => ResolutionAnswerWith (F i) (E i))
      (fun i => @ResolutionAnswerWith.realize (F i) (E i))
      (fun i q =>
        (ResolutionAnswerWith.residual q :
          ResolutionAnswerWith (F i) (E i))) := by
  intro Y onSolution onResidual
  let f : (i : I) -> ResolutionAnswerWith (F i) (E i) -> Y i :=
    fun i => ResolutionAnswerWith.fold (onSolution i) (onResidual i)
  refine ⟨f, ?_, ?_⟩
  · constructor
    · intro i x
      cases x
      rfl
    · intro i q
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
    | residual q =>
        have h := hg.2 i q
        change g i
          (ResolutionAnswerWith.residual q :
            ResolutionAnswerWith (F i) (E i)) = onResidual i q at h
        change g i
          (ResolutionAnswerWith.residual q :
            ResolutionAnswerWith (F i) (E i)) = onResidual i q
        exact h

/-- A family equivalence is structural when it preserves every ordinary
solution generator and every residual-provenance generator in every fiber. -/
def IsStructuralResidualFamilyEquiv
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (X : I -> Type (max u r))
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (includeResidual : (i : I) -> E i -> X i)
    (e : (i : I) ->
      Equiv (X i) (ResolutionAnswerWith (F i) (E i))) : Prop :=
  (forall (i : I) (x : Specification.Solution (F i)),
      e i (includeSolution i x) = ResolutionAnswerWith.realize x) ∧
    forall (i : I) (q : E i),
      e i (includeResidual i q) =
        (ResolutionAnswerWith.residual q :
          ResolutionAnswerWith (F i) (E i))

/-- Global structured canonicity.  Every simultaneous universal residual
extension is uniquely equivalent, as one dependent family, to the canonical
structured Resolution family. -/
theorem universalResidualExtensionFamily_unique_structural_equiv
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (X : I -> Type (max u r))
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (includeResidual : (i : I) -> E i -> X i)
    (hX : IsUniversalResidualExtensionFamily
      F E X includeSolution includeResidual) :
    Exists fun e : (i : I) ->
        Equiv (X i) (ResolutionAnswerWith (F i) (E i)) =>
      IsStructuralResidualFamilyEquiv
        F E X includeSolution includeResidual e ∧
      forall g : (i : I) ->
          Equiv (X i) (ResolutionAnswerWith (F i) (E i)),
        IsStructuralResidualFamilyEquiv
          F E X includeSolution includeResidual g ->
        g = e := by
  rcases hX
      (fun i => ResolutionAnswerWith (F i) (E i))
      (fun i => @ResolutionAnswerWith.realize (F i) (E i))
      (fun i q =>
        (ResolutionAnswerWith.residual q :
          ResolutionAnswerWith (F i) (E i))) with
    ⟨toCanonical, hto, htoUnique⟩
  rcases resolutionAnswerWithFamily_isUniversalResidualExtension F E
      X includeSolution includeResidual with
    ⟨fromCanonical, hfrom, _⟩
  have hleftFamily :
      (fun (i : I) (z : X i) =>
        fromCanonical i (toCanonical i z)) =
      (fun (i : I) (z : X i) => z) := by
    have hcompPreserves :
        ((forall (i : I) (x : Specification.Solution (F i)),
            fromCanonical i (toCanonical i (includeSolution i x)) =
              includeSolution i x) ∧
          (forall (i : I) (q : E i),
            fromCanonical i (toCanonical i (includeResidual i q)) =
              includeResidual i q)) := by
      constructor
      · intro i x
        calc
          fromCanonical i (toCanonical i (includeSolution i x)) =
              fromCanonical i (ResolutionAnswerWith.realize x) :=
            congrArg (fromCanonical i) (hto.1 i x)
          _ = includeSolution i x := hfrom.1 i x
      · intro i q
        calc
          fromCanonical i (toCanonical i (includeResidual i q)) =
              fromCanonical i
                (ResolutionAnswerWith.residual q :
                  ResolutionAnswerWith (F i) (E i)) :=
            congrArg (fromCanonical i) (hto.2 i q)
          _ = includeResidual i q := hfrom.2 i q
    have hidPreserves :
        ((forall (i : I) (x : Specification.Solution (F i)),
            (fun z : X i => z) (includeSolution i x) =
              includeSolution i x) ∧
          (forall (i : I) (q : E i),
            (fun z : X i => z) (includeResidual i q) =
              includeResidual i q)) := by
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    rcases hX X includeSolution includeResidual with
      ⟨k, _, hUnique⟩
    have hc :
        (fun (i : I) (z : X i) =>
          fromCanonical i (toCanonical i z)) = k :=
      hUnique _ hcompPreserves
    have hi : (fun (i : I) (z : X i) => z) = k :=
      hUnique _ hidPreserves
    exact hc.trans hi.symm
  let e : (i : I) ->
      Equiv (X i) (ResolutionAnswerWith (F i) (E i)) :=
    fun i => {
      toFun := toCanonical i
      invFun := fromCanonical i
      left_inv := by
        intro x
        exact congrArg (fun k => k i x) hleftFamily
      right_inv := by
        intro a
        cases a with
        | realized x hx =>
            let sx : Specification.Solution (F i) := ⟨x, hx⟩
            calc
              toCanonical i (fromCanonical i (.realized x hx)) =
                  toCanonical i
                    (fromCanonical i (ResolutionAnswerWith.realize sx)) := by
                rfl
              _ = toCanonical i (includeSolution i sx) :=
                congrArg (toCanonical i) (hfrom.1 i sx)
              _ = ResolutionAnswerWith.realize sx := hto.1 i sx
              _ = .realized x hx := by rfl
        | residual q =>
            calc
              toCanonical i (fromCanonical i
                  (ResolutionAnswerWith.residual q :
                    ResolutionAnswerWith (F i) (E i))) =
                  toCanonical i (includeResidual i q) :=
                congrArg (toCanonical i) (hfrom.2 i q)
              _ = (ResolutionAnswerWith.residual q :
                    ResolutionAnswerWith (F i) (E i)) :=
                hto.2 i q
    }
  refine ⟨e, ?_, ?_⟩
  · constructor
    · intro i x
      change toCanonical i (includeSolution i x) =
        ResolutionAnswerWith.realize x
      exact hto.1 i x
    · intro i q
      change toCanonical i (includeResidual i q) =
        (ResolutionAnswerWith.residual q :
          ResolutionAnswerWith (F i) (E i))
      exact hto.2 i q
  · intro g hg
    have hgFun :
        (fun (i : I) (x : X i) => g i x) = toCanonical := by
      exact htoUnique (fun i x => g i x) hg
    funext i
    apply Equiv.ext
    funext x
    exact congrArg (fun k => k i x) hgFun

/-- Exact fiberwise inhabitation criterion for any universal structured family.
A fiber is inhabited exactly when it has an ordinary solution or its chosen
residual vocabulary is inhabited. -/
theorem universalResidualExtensionFamily_nonempty_iff
    {I : Type v}
    (F : I -> Specification.{u})
    (E : I -> Type r)
    (X : I -> Type (max u r))
    (includeSolution :
      (i : I) -> Specification.Solution (F i) -> X i)
    (includeResidual : (i : I) -> E i -> X i)
    (hX : IsUniversalResidualExtensionFamily
      F E X includeSolution includeResidual) :
    forall i : I,
      Nonempty (X i) ↔
        Specification.Satisfiable (F i) ∨ Nonempty (E i) := by
  intro i
  constructor
  · intro hNonempty
    rcases hNonempty with ⟨z⟩
    rcases hX
        (fun j => ResolutionAnswerWith (F j) (E j))
        (fun j => @ResolutionAnswerWith.realize (F j) (E j))
        (fun j q =>
          (ResolutionAnswerWith.residual q :
            ResolutionAnswerWith (F j) (E j))) with
      ⟨toCanonical, _, _⟩
    cases toCanonical i z with
    | realized x hx =>
        exact Or.inl ⟨x, hx⟩
    | residual q =>
        exact Or.inr ⟨q⟩
  · intro h
    cases h with
    | inl hs =>
        rcases hs with ⟨x, hx⟩
        exact ⟨includeSolution i ⟨x, hx⟩⟩
    | inr he =>
        rcases he with ⟨q⟩
        exact ⟨includeResidual i q⟩

end StrongTotality
end Resolution
