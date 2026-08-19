import ResolutionStrongTotalityDependent

/-!
# Structured residuals for Strong Totality

The minimal Strong Totality construction uses one residual point.  That is the
right free pointed completion when the only question is whether an ordinary
solution has been obtained.  Composite mathematics may need more provenance:
which stage remained unresolved, which earlier certified data had already been
obtained, or which residual class should be retained.

The clean generalization is to parameterize Resolution Answers by a residual
type `E`.  The resulting construction is the free extension of the ordinary
solution type by `E`.  The original one-residual theory is exactly the special
case `E = Unit`.

The residual vocabulary may live in a universe different from the candidate
space.  This matters for kernel provenance, where operation symbols and carrier
values can inhabit independent universes.

For dependent two-stage specifications we then choose a residual type with two
forms: the first stage is unresolved, or the first stage has a certified
solution and the second stage is unresolved.  A canonical coarsening map
forgets this provenance and recovers the earlier single-residual semantics.
-/

universe u r w

namespace Resolution
namespace StrongTotality

inductive ResolutionAnswerWith
    (S : Specification.{u}) (E : Type r) : Type (max u r) where
  | realized (x : S.Candidate) (hx : S.accepts x)
  | residual (e : E)

namespace ResolutionAnswerWith

def realize
    {S : Specification.{u}} {E : Type r}
    (x : Specification.Solution S) : ResolutionAnswerWith S E :=
  .realized x.1 x.2

def fold
    {S : Specification.{u}} {E : Type r} {X : Type w}
    (onSolution : Specification.Solution S -> X)
    (onResidual : E -> X) :
    ResolutionAnswerWith S E -> X
  | .realized x hx => onSolution ⟨x, hx⟩
  | .residual e => onResidual e

@[simp] theorem fold_realized
    {S : Specification.{u}} {E : Type r} {X : Type w}
    (onSolution : Specification.Solution S -> X)
    (onResidual : E -> X)
    (x : S.Candidate) (hx : S.accepts x) :
    fold onSolution onResidual (.realized x hx) = onSolution ⟨x, hx⟩ := by
  rfl

@[simp] theorem fold_residual
    {S : Specification.{u}} {E : Type r} {X : Type w}
    (onSolution : Specification.Solution S -> X)
    (onResidual : E -> X)
    (e : E) :
    fold onSolution onResidual (.residual e : ResolutionAnswerWith S E) =
      onResidual e := by
  rfl

def equivSum
    (S : Specification.{u}) (E : Type r) :
    Equiv (ResolutionAnswerWith S E) (Sum (Specification.Solution S) E) where
  toFun := fun a =>
    match a with
    | .realized x hx => .inl ⟨x, hx⟩
    | .residual e => .inr e
  invFun := fun z =>
    match z with
    | .inl x => realize x
    | .inr e => .residual e
  left_inv := by
    intro a
    cases a <;> rfl
  right_inv := by
    intro z
    cases z <;> rfl

end ResolutionAnswerWith

def IsUniversalResidualExtension
    (S : Specification.{u})
    (E : Type r)
    (X : Type (max u r))
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X) : Prop :=
  forall (Y : Type (max u r))
      (onSolution : Specification.Solution S -> Y)
      (onResidual : E -> Y),
    Exists fun f : X -> Y =>
      ((forall x : Specification.Solution S,
          f (includeSolution x) = onSolution x) ∧
        (forall e : E, f (includeResidual e) = onResidual e)) ∧
      forall g : X -> Y,
        ((forall x : Specification.Solution S,
            g (includeSolution x) = onSolution x) ∧
          (forall e : E, g (includeResidual e) = onResidual e)) ->
        g = f

theorem resolutionAnswerWith_isUniversalResidualExtension
    (S : Specification.{u}) (E : Type r) :
    IsUniversalResidualExtension S E (ResolutionAnswerWith S E)
      (@ResolutionAnswerWith.realize S E)
      (fun e => ResolutionAnswerWith.residual e) := by
  intro Y onSolution onResidual
  let f : ResolutionAnswerWith S E -> Y :=
    ResolutionAnswerWith.fold onSolution onResidual
  refine ⟨f, ?_, ?_⟩
  · constructor
    · intro x
      cases x
      rfl
    · intro e
      rfl
  · intro g hg
    funext a
    cases a with
    | realized x hx =>
        have h := hg.1 (⟨x, hx⟩ : Specification.Solution S)
        simpa [f, ResolutionAnswerWith.realize] using h
    | residual e =>
        simpa [f] using hg.2 e

theorem strongTotalityWith
    (S : Specification.{u})
    {E : Type r}
    (e : E) :
    Nonempty (ResolutionAnswerWith S E) := by
  exact ⟨.residual e⟩

def coarsenResidual
    {S : Specification.{u}} {E : Type r} :
    ResolutionAnswerWith S E -> ResolutionAnswer S
  | .realized x hx => .realized x hx
  | .residual _ => .residual

@[simp] theorem coarsenResidual_realized
    {S : Specification.{u}} {E : Type r}
    (x : S.Candidate) (hx : S.accepts x) :
    coarsenResidual (.realized x hx : ResolutionAnswerWith S E) =
      (.realized x hx : ResolutionAnswer S) := by
  rfl

@[simp] theorem coarsenResidual_residual
    {S : Specification.{u}} {E : Type r}
    (e : E) :
    coarsenResidual (.residual e : ResolutionAnswerWith S E) =
      (ResolutionAnswer.residual : ResolutionAnswer S) := by
  rfl

def unitResidualEquiv
    (S : Specification.{u}) :
    Equiv (ResolutionAnswerWith S Unit) (ResolutionAnswer S) where
  toFun := coarsenResidual
  invFun := fun a =>
    match a with
    | .realized x hx => .realized x hx
    | .residual => .residual ()
  left_inv := by
    intro a
    cases a with
    | realized x hx => rfl
    | residual e =>
        cases e
        rfl
  right_inv := by
    intro a
    cases a <;> rfl

inductive DependentResidual (S : Specification.{u}) : Type u where
  | first
  | second (sx : Specification.Solution S)

abbrev StructuredDependentAnswer
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) : Type u :=
  ResolutionAnswerWith (dependentSpecification S T) (DependentResidual S)

def structuredTotalizeAt
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S) :
    Option (Specification.Solution (T sx)) -> StructuredDependentAnswer S T
  | none => .residual (.second sx)
  | some sy => .realized ⟨sx, sy.1⟩ sy.2

def structuredTotalizeDependent
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : Option (Specification.Solution S))
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    StructuredDependentAnswer S T :=
  match first with
  | none => .residual .first
  | some sx => structuredTotalizeAt S T sx (second sx)

theorem structuredTotalizeDependent_some
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S)
    (second : (s : Specification.Solution S) ->
      Option (Specification.Solution (T s))) :
    structuredTotalizeDependent S T (some sx) second =
      structuredTotalizeAt S T sx (second sx) := by
  rfl

@[simp] theorem structuredTotalizeDependent_first_none
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    structuredTotalizeDependent S T none second = .residual .first := by
  rfl

@[simp] theorem structuredTotalizeDependent_second_none
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S)
    (second : (s : Specification.Solution S) ->
      Option (Specification.Solution (T s)))
    (h : second sx = none) :
    structuredTotalizeDependent S T (some sx) second =
      .residual (.second sx) := by
  rw [structuredTotalizeDependent_some S T sx second, h]
  rfl

@[simp] theorem structuredTotalizeDependent_realized
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S)
    (second : (s : Specification.Solution S) ->
      Option (Specification.Solution (T s)))
    (sy : Specification.Solution (T sx))
    (h : second sx = some sy) :
    structuredTotalizeDependent S T (some sx) second =
      (.realized ⟨sx, sy.1⟩ sy.2 : StructuredDependentAnswer S T) := by
  rw [structuredTotalizeDependent_some S T sx second, h]
  rfl

theorem coarsen_structuredTotalizeDependent
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : Option (Specification.Solution S))
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    coarsenResidual (structuredTotalizeDependent S T first second) =
      totalizeDependent S T first second := by
  cases first with
  | none => rfl
  | some sx =>
      cases h : second sx with
      | none =>
          rw [structuredTotalizeDependent_second_none S T sx second h]
          rw [totalizeDependent_second_none S T sx second h]
          rfl
      | some sy =>
          rw [structuredTotalizeDependent_realized S T sx second sy h]
          rw [totalizeDependent_realized S T sx second sy h]
          rfl

theorem structuredCoarsening_surjective
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    Function.Surjective
      (@coarsenResidual (dependentSpecification S T) (DependentResidual S)) := by
  intro a
  cases a with
  | residual =>
      exact ⟨.residual .first, rfl⟩
  | realized z hz =>
      exact ⟨.realized z hz, rfl⟩

theorem structuredCoarsening_not_injective
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S) :
    ¬ Function.Injective
      (@coarsenResidual (dependentSpecification S T) (DependentResidual S)) := by
  intro hinj
  have h := hinj
    (show coarsenResidual
        (.residual (.first) : StructuredDependentAnswer S T) =
      coarsenResidual
        (.residual (.second sx) : StructuredDependentAnswer S T) by rfl)
  cases h

theorem structuredDependent_isUniversal
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    IsUniversalResidualExtension
      (dependentSpecification S T)
      (DependentResidual S)
      (StructuredDependentAnswer S T)
      (@ResolutionAnswerWith.realize
        (dependentSpecification S T) (DependentResidual S))
      (fun e => ResolutionAnswerWith.residual e) :=
  resolutionAnswerWith_isUniversalResidualExtension
    (dependentSpecification S T) (DependentResidual S)

end StrongTotality
end Resolution