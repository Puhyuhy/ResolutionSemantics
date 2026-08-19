import ResolutionStrongTotalityComposition

/-!
# Dependent Strong Totality

Sequential mathematical specifications are often genuinely dependent: the
second problem is not fixed in advance, but is determined by a certified
solution of the first.  A fixed-target Kleisli arrow cannot express this
without erasing information when the first stage is unresolved.

The type-theoretically natural construction is instead the dependent sum of
specifications.  A candidate for the composite problem contains a certified
solution of the first specification together with a candidate for the second
specification selected by that solution.  This construction is itself a
well-formed specification, so Strong Totality applies to it directly.

Thus the universal principle is closed under dependent mathematical
construction, not merely under fixed-target sequential composition.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- The dependent sum of a specification `S` and a family of specifications
`T` indexed by certified solutions of `S`.

A candidate contains the first certified solution already, because only such a
solution determines which second specification is meaningful.  Acceptance then
requires that the second candidate satisfy that selected specification. -/
def dependentSpecification
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) : Specification.{u} where
  Candidate := Sigma fun sx : Specification.Solution S => (T sx).Candidate
  accepts := fun z => (T z.1).accepts z.2

/-- Ordinary solutions of the dependent specification are exactly dependent
pairs of ordinary solutions. -/
def dependentSolutionEquiv
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    Equiv (Specification.Solution (dependentSpecification S T))
      (Sigma fun sx : Specification.Solution S => Specification.Solution (T sx)) where
  toFun := fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv := by
    intro z
    cases z with
    | mk z hz =>
      cases z
      rfl
  right_inv := by
    intro z
    cases z with
    | mk sx sy =>
      cases sy
      rfl

/-- Strong Totality is closed under dependent sums: every dependent
mathematical construction has a Resolution Answer even when no ordinary
composite solution is available. -/
theorem dependentStrongTotality
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    Nonempty (ResolutionAnswer (dependentSpecification S T)) :=
  strongTotality (dependentSpecification S T)

/-! ## Partial dependent resolution -/

/-- Package a certified second-stage solution together with the certified
first-stage solution that selected its specification. -/
def dependentPairSolution
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S)
    (sy : Specification.Solution (T sx)) :
    Specification.Solution (dependentSpecification S T) :=
  ⟨⟨sx, sy.1⟩, sy.2⟩

/-- Lift one optional second-stage solution after its first-stage index has
already been fixed.  Isolating this dependent match keeps the index stable. -/
def dependentPartialAt
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S) :
    Option (Specification.Solution (T sx)) ->
      Option (Specification.Solution (dependentSpecification S T))
  | none => none
  | some sy => some (dependentPairSolution S T sx sy)

/-- Compose an ordinary partial solution of `S` with a partial solution of the
second specification selected by the first solution. -/
def dependentPartialCompose
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : Option (Specification.Solution S))
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    Option (Specification.Solution (dependentSpecification S T)) :=
  match first with
  | none => none
  | some sx => dependentPartialAt S T sx (second sx)

/-- Total dependent resolution.  Failure of either ordinary stage becomes the
single canonical residual of the composite dependent specification. -/
def totalizeDependent
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : Option (Specification.Solution S))
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    ResolutionAnswer (dependentSpecification S T) :=
  totalize (dependentSpecification S T)
    (dependentPartialCompose S T first second)

@[simp] theorem totalizeDependent_first_none
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    totalizeDependent S T none second = .residual := by
  rfl

@[simp] theorem totalizeDependent_second_none
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S)
    (second : (s : Specification.Solution S) ->
      Option (Specification.Solution (T s)))
    (h : second sx = none) :
    totalizeDependent S T (some sx) second = .residual := by
  have hcompose :
      dependentPartialCompose S T (some sx) second = none := by
    unfold dependentPartialCompose
    rw [h]
    rfl
  unfold totalizeDependent
  rw [hcompose]
  rfl

@[simp] theorem totalizeDependent_realized
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (sx : Specification.Solution S)
    (second : (s : Specification.Solution S) ->
      Option (Specification.Solution (T s)))
    (sy : Specification.Solution (T sx))
    (h : second sx = some sy) :
    totalizeDependent S T (some sx) second =
      realizeSolution (dependentPairSolution S T sx sy) := by
  have hcompose :
      dependentPartialCompose S T (some sx) second =
        some (dependentPairSolution S T sx sy) := by
    unfold dependentPartialCompose
    rw [h]
    rfl
  unfold totalizeDependent
  rw [hcompose]
  rfl

/-- Totalizing the dependent computation is exactly the canonical Strong
Totality totalization of its ordinary partial composite.  This theorem records
that no extra choice or ad-hoc dependent failure semantics has been introduced. -/
theorem totalizeDependent_eq_canonical
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (first : Option (Specification.Solution S))
    (second : (sx : Specification.Solution S) ->
      Option (Specification.Solution (T sx))) :
    totalizeDependent S T first second =
      totalize (dependentSpecification S T)
        (dependentPartialCompose S T first second) := by
  rfl

/-! ## Iterated dependent construction -/

/-- Three dependent stages can be represented by iterating the same dependent
specification constructor.  The third specification may depend on the entire
certified solution of the first two stages. -/
def dependentSpecification3
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (U : Specification.Solution (dependentSpecification S T) -> Specification.{u}) :
    Specification.{u} :=
  dependentSpecification (dependentSpecification S T) U

/-- Strong Totality immediately extends to three dependent stages. -/
theorem dependentStrongTotality3
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u})
    (U : Specification.Solution (dependentSpecification S T) -> Specification.{u}) :
    Nonempty (ResolutionAnswer (dependentSpecification3 S T U)) :=
  strongTotality (dependentSpecification3 S T U)

/-- More generally, any already-constructed dependent specification can be
extended by one further dependent stage while preserving Strong Totality. -/
theorem dependentStrongTotality_step
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    Nonempty (ResolutionAnswer (dependentSpecification S T)) :=
  dependentStrongTotality S T

end StrongTotality
end Resolution
