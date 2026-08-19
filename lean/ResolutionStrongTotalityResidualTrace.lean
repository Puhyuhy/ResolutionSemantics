import ResolutionStrongTotalityResidualRefinement

/-!
# Typed residual traces for dependent composition

Structured Strong Totality should retain not only the fact that a dependent
computation remained unresolved, but the exact residual information produced at
the stage where resolution stopped and the certified progress obtained before
that point.

For a first specification `S` with residual vocabulary `E`, and a dependent
second specification `T sx` whose residual vocabulary is `F sx`, the minimal
trace shape is

  E + Sigma sx : Solution S, F sx.

A left trace records a residual from the first stage.  A right trace records the
certified first-stage solution together with the residual produced by the
selected second stage.  No additional trace states are needed.

The corresponding dependent bind preserves realized solutions, injects first-
and second-stage residuals into their typed trace positions, and coarsens
exactly to the earlier one-residual dependent semantics.  Forgetting residual
payloads while retaining only the stage recovers the earlier
`DependentResidual` vocabulary.
-/

universe u r s

namespace Resolution
namespace StrongTotality

/-- The typed residual trace of a two-stage dependent computation. -/
abbrev DependentResidualTrace
    (S : Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s) :
    Type (max r (max u s)) :=
  Sum E (Sigma fun sx : Specification.Solution S => F sx)

namespace DependentResidualTrace

/-- A first-stage residual terminates the computation before any certified
first-stage solution is available. -/
def first
    {S : Specification.{u}}
    {E : Type r}
    {F : Specification.Solution S -> Type s}
    (e : E) : DependentResidualTrace S E F :=
  Sum.inl e

/-- A second-stage residual records the certified first-stage solution that
selected the second specification together with its residual payload. -/
def second
    {S : Specification.{u}}
    {E : Type r}
    {F : Specification.Solution S -> Type s}
    (sx : Specification.Solution S)
    (q : F sx) : DependentResidualTrace S E F :=
  Sum.inr ⟨sx, q⟩

/-- Forget residual payloads but retain the stage at which resolution stopped
and, for second-stage failure, the certified first-stage solution. -/
def forgetStage
    {S : Specification.{u}}
    {E : Type r}
    {F : Specification.Solution S -> Type s} :
    DependentResidualTrace S E F -> DependentResidual S
  | .inl _ => .first
  | .inr z => .second z.1

end DependentResidualTrace

/-- Structured answers for a dependent computation carrying the full typed
residual trace. -/
abbrev TracedDependentAnswer
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s) :=
  ResolutionAnswerWith
    (dependentSpecification S T)
    (DependentResidualTrace S E F)

/-- Continue a dependent computation after a certified first-stage solution has
already been obtained. -/
def tracedDependentAt
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (sx : Specification.Solution S) :
    ResolutionAnswerWith (T sx) (F sx) ->
      TracedDependentAnswer S T E F
  | .realized y hy => .realized ⟨sx, y⟩ hy
  | .residual q => .residual (DependentResidualTrace.second sx q)

/-- Typed dependent bind.  A residual from the first stage is retained as a
first-stage trace.  A realized first stage selects the second computation; a
second-stage residual then retains both the certified first-stage solution and
the second residual payload. -/
def tracedDependentBind
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (first : ResolutionAnswerWith S E)
    (second : (sx : Specification.Solution S) ->
      ResolutionAnswerWith (T sx) (F sx)) :
    TracedDependentAnswer S T E F :=
  match first with
  | .residual e => .residual (DependentResidualTrace.first e)
  | .realized x hx =>
      tracedDependentAt S T E F ⟨x, hx⟩ (second ⟨x, hx⟩)

@[simp] theorem tracedDependentBind_first_residual
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (e : E)
    (second : (sx : Specification.Solution S) ->
      ResolutionAnswerWith (T sx) (F sx)) :
    tracedDependentBind S T E F
        (.residual e : ResolutionAnswerWith S E) second =
      .residual (DependentResidualTrace.first e) := by
  rfl

@[simp] theorem tracedDependentBind_second_residual
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (sx : Specification.Solution S)
    (second : (s0 : Specification.Solution S) ->
      ResolutionAnswerWith (T s0) (F s0))
    (q : F sx)
    (h : second sx = .residual q) :
    tracedDependentBind S T E F
        (ResolutionAnswerWith.realize sx) second =
      .residual (DependentResidualTrace.second sx q) := by
  cases sx with
  | mk x hx =>
      change tracedDependentAt S T E F ⟨x, hx⟩ (second ⟨x, hx⟩) =
        .residual (DependentResidualTrace.second ⟨x, hx⟩ q)
      rw [h]
      rfl

@[simp] theorem tracedDependentBind_realized
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (sx : Specification.Solution S)
    (second : (s0 : Specification.Solution S) ->
      ResolutionAnswerWith (T s0) (F s0))
    (sy : Specification.Solution (T sx))
    (h : second sx = ResolutionAnswerWith.realize sy) :
    tracedDependentBind S T E F
        (ResolutionAnswerWith.realize sx) second =
      ResolutionAnswerWith.realize (dependentPairSolution S T sx sy) := by
  cases sx with
  | mk x hx =>
      cases sy with
      | mk y hy =>
          change tracedDependentAt S T E F ⟨x, hx⟩ (second ⟨x, hx⟩) =
            (.realized ⟨⟨x, hx⟩, y⟩ hy : TracedDependentAnswer S T E F)
          rw [h]
          rfl

namespace ResolutionAnswer

/-- Minimal dependent bind obtained by forgetting all residual provenance. -/
def bindDependent
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : ResolutionAnswer S)
    (second : (sx : Specification.Solution S) -> ResolutionAnswer (T sx)) :
    ResolutionAnswer (dependentSpecification S T) :=
  match first with
  | .residual => .residual
  | .realized x hx =>
      match second ⟨x, hx⟩ with
      | .residual => .residual
      | .realized y hy => .realized ⟨⟨x, hx⟩, y⟩ hy

end ResolutionAnswer

/-- Typed dependent bind is a provenance refinement of minimal dependent bind:
forgetting the full trace gives exactly the same minimal Resolution Answer. -/
theorem coarsen_tracedDependentBind
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (first : ResolutionAnswerWith S E)
    (second : (sx : Specification.Solution S) ->
      ResolutionAnswerWith (T sx) (F sx)) :
    coarsenResidual (tracedDependentBind S T E F first second) =
      ResolutionAnswer.bindDependent S T
        (coarsenResidual first)
        (fun sx => coarsenResidual (second sx)) := by
  cases first with
  | residual e =>
      rfl
  | realized x hx =>
      cases h : second ⟨x, hx⟩ with
      | residual q =>
          change coarsenResidual
              (tracedDependentAt S T E F ⟨x, hx⟩
                (.residual q : ResolutionAnswerWith (T ⟨x, hx⟩) (F ⟨x, hx⟩))) =
            ResolutionAnswer.bindDependent S T
              (.realized x hx)
              (fun sx => coarsenResidual (second sx))
          rw [h]
          rfl
      | realized y hy =>
          change coarsenResidual
              (tracedDependentAt S T E F ⟨x, hx⟩
                (.realized y hy : ResolutionAnswerWith (T ⟨x, hx⟩) (F ⟨x, hx⟩))) =
            ResolutionAnswer.bindDependent S T
              (.realized x hx)
              (fun sx => coarsenResidual (second sx))
          rw [h]
          rfl

/-- Stage-only dependent bind.  This retains where resolution stopped but
forgets the actual residual payloads. -/
def stageDependentBind
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (first : ResolutionAnswerWith S E)
    (second : (sx : Specification.Solution S) ->
      ResolutionAnswerWith (T sx) (F sx)) :
    StructuredDependentAnswer S T :=
  match first with
  | .residual _ => .residual .first
  | .realized x hx =>
      match second ⟨x, hx⟩ with
      | .residual _ => .residual (.second ⟨x, hx⟩)
      | .realized y hy => .realized ⟨⟨x, hx⟩, y⟩ hy

/-- Forgetting residual payloads from the typed trace recovers exactly the
stage-only dependent semantics. -/
theorem forgetStage_tracedDependentBind
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s)
    (first : ResolutionAnswerWith S E)
    (second : (sx : Specification.Solution S) ->
      ResolutionAnswerWith (T sx) (F sx)) :
    ResolutionAnswerWith.mapResidual
        (@DependentResidualTrace.forgetStage S E F)
        (tracedDependentBind S T E F first second) =
      stageDependentBind S T E F first second := by
  cases first with
  | residual e =>
      rfl
  | realized x hx =>
      cases h : second ⟨x, hx⟩ with
      | residual q =>
          change ResolutionAnswerWith.mapResidual
              (@DependentResidualTrace.forgetStage S E F)
              (tracedDependentAt S T E F ⟨x, hx⟩
                (.residual q : ResolutionAnswerWith (T ⟨x, hx⟩) (F ⟨x, hx⟩))) =
            stageDependentBind S T E F
              (.realized x hx : ResolutionAnswerWith S E) second
          rw [h]
          rfl
      | realized y hy =>
          change ResolutionAnswerWith.mapResidual
              (@DependentResidualTrace.forgetStage S E F)
              (tracedDependentAt S T E F ⟨x, hx⟩
                (.realized y hy : ResolutionAnswerWith (T ⟨x, hx⟩) (F ⟨x, hx⟩))) =
            stageDependentBind S T E F
              (.realized x hx : ResolutionAnswerWith S E) second
          rw [h]
          rfl

/-- The traced dependent answer space is the canonical universal extension for
its typed trace vocabulary. -/
theorem tracedDependent_isUniversal
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (E : Type r)
    (F : Specification.Solution S -> Type s) :
    IsUniversalResidualExtension
      (dependentSpecification S T)
      (DependentResidualTrace S E F)
      (TracedDependentAnswer S T E F)
      (@ResolutionAnswerWith.realize
        (dependentSpecification S T) (DependentResidualTrace S E F))
      (fun q => ResolutionAnswerWith.residual q) :=
  resolutionAnswerWith_isUniversalResidualExtension
    (dependentSpecification S T) (DependentResidualTrace S E F)

end StrongTotality
end Resolution
