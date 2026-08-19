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

For dependent two-stage specifications we then choose a residual type with two
forms: the first stage is unresolved, or the first stage has a certified
solution and the second stage is unresolved.  A canonical coarsening map
forgets this provenance and recovers the earlier single-residual semantics.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- Resolution Answers with an arbitrary typed residual vocabulary `E`. -/
inductive ResolutionAnswerWith
    (S : Specification.{u}) (E : Type u) : Type u where
  | realized (x : S.Candidate) (hx : S.accepts x)
  | residual (e : E)

namespace ResolutionAnswerWith

/-- Embed an ordinary satisfying solution. -/
def realize
    {S : Specification.{u}} {E : Type u}
    (x : Specification.Solution S) : ResolutionAnswerWith S E :=
  .realized x.1 x.2

/-- Interpret a structured Resolution Answer by separately interpreting
ordinary solutions and residual data. -/
def fold
    {S : Specification.{u}} {E X : Type u}
    (onSolution : Specification.Solution S -> X)
    (onResidual : E -> X) :
    ResolutionAnswerWith S E -> X
  | .realized x hx => onSolution ⟨x, hx⟩
  | .residual e => onResidual e

@[simp] theorem fold_realized
    {S : Specification.{u}} {E X : Type u}
    (onSolution : Specification.Solution S -> X)
    (onResidual : E -> X)
    (x : S.Candidate) (hx : S.accepts x) :
    fold onSolution onResidual (.realized x hx) = onSolution ⟨x, hx⟩ := by
  rfl

@[simp] theorem fold_residual
    {S : Specification.{u}} {E X : Type u}
    (onSolution : Specification.Solution S -> X)
    (onResidual : E -> X)
    (e : E) :
    fold onSolution onResidual (.residual e : ResolutionAnswerWith S E) =
      onResidual e := by
  rfl

/-- Structured Resolution Answers contain exactly either an ordinary solution
or one residual datum. -/
def equivSum
    (S : Specification.{u}) (E : Type u) :
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

/-- Universal property for adjoining an arbitrary residual type to ordinary
solutions. -/
def IsUniversalResidualExtension
    (S : Specification.{u})
    (E X : Type u)
    (includeSolution : Specification.Solution S -> X)
    (includeResidual : E -> X) : Prop :=
  forall (Y : Type u)
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

/-- `ResolutionAnswerWith S E` is the free extension of the solution type by
exactly the residual vocabulary `E`. -/
theorem resolutionAnswerWith_isUniversalResidualExtension
    (S : Specification.{u}) (E : Type u) :
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

/-- If the residual vocabulary is inhabited, structured Strong Totality holds
for every well-formed specification. -/
theorem strongTotalityWith
    (S : Specification.{u})
    {E : Type u}
    (e : E) :
    Nonempty (ResolutionAnswerWith S E) := by
  exact ⟨.residual e⟩

/-- Forget all residual provenance and return to the minimal single-residual
Strong Totality semantics. -/
def coarsenResidual
    {S : Specification.{u}} {E : Type u} :
    ResolutionAnswerWith S E -> ResolutionAnswer S
  | .realized x hx => .realized x hx
  | .residual _ => .residual

@[simp] theorem coarsenResidual_realized
    {S : Specification.{u}} {E : Type u}
    (x : S.Candidate) (hx : S.accepts x) :
    coarsenResidual (.realized x hx : ResolutionAnswerWith S E) =
      (.realized x hx : ResolutionAnswer S) := by
  rfl

@[simp] theorem coarsenResidual_residual
    {S : Specification.{u}} {E : Type u}
    (e : E) :
    coarsenResidual (.residual e : ResolutionAnswerWith S E) =
      (ResolutionAnswer.residual : ResolutionAnswer S) := by
  rfl

/-- The original Strong Totality answer type is precisely the one-residual
instance of the structured construction. -/
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

/-! ## Provenance-preserving dependent resolution -/

/-- Residual provenance for a two-stage dependent specification.

`first` means no ordinary solution of the first stage was supplied.
`second sx` records that the first stage was solved by `sx`, but the dependent
second stage selected by `sx` remained unresolved. -/
inductive DependentResidual (S : Specification.{u}) : Type u where
  | first
  | second (sx : Specification.Solution S)

/-- The provenance-preserving answer type for a two-stage dependent problem. -/
abbrev StructuredDependentAnswer
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) : Type u :=
  ResolutionAnswerWith (dependentSpecification S T) (DependentResidual S)

/-- Totalize a dependent two-stage computation while preserving the exact
stage at which ordinary resolution stopped. -/
def structuredTotalizeDependent
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : Option (Specification.Solution S))
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    StructuredDependentAnswer S T :=
  match first with
  | none => .residual .first
  | some sx =>
      match second sx with
      | none => .residual (.second sx)
      | some sy => .realized ⟨sx, sy.1⟩ sy.2

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
  simp [structuredTotalizeDependent, h]

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
  simp [structuredTotalizeDependent, h]

/-- Forgetting provenance after structured dependent totalization gives exactly
the earlier canonical one-residual dependent totalization. -/
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
      cases second sx <;> rfl

/-- Every coarse dependent Resolution Answer has a provenance-preserving
refinement.  The coarse residual may always be refined as a first-stage
residual; realized answers refine canonically. -/
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

/-- When the first specification has a certified solution, the structured
semantics genuinely contains more information than the coarse one: first-stage
and second-stage residual provenance are distinct but coarsen to the same
single residual. -/
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

/-- The provenance-preserving dependent answer type inherits a universal
property immediately: it is the free extension of ordinary dependent solutions
by exactly the two-stage residual vocabulary. -/
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
