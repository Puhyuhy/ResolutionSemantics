import ResolutionStrongTotalityResidualStructure

/-!
# Refinement and coarsening of residual semantics

Structured Strong Totality separates the existence of Resolution Answers from
how much information residual answers retain.  A map `E -> F` between residual
vocabularies is read from finer to coarser information: each residual datum in
`E` is translated into one in `F`.

Such maps lift canonically to Resolution Answers, fix every realized ordinary
solution, and compose functorially.  The one-point residual vocabulary `Unit`
is terminal: every residual vocabulary has exactly one map to it.  Consequently
the original single-residual Strong Totality semantics is the unique coarsest
semantics obtained by forgetting all residual provenance while preserving every
ordinary solution.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- A refinement/coarsening map between residual vocabularies.  The direction
`E -> F` means that an `E`-residual may retain at least as much provenance as
its image in `F`. -/
abbrev ResidualRefinement (E F : Type u) : Type u := E -> F

namespace ResidualRefinement

/-- Identity residual translation. -/
def id (E : Type u) : ResidualRefinement E E :=
  fun e => e

/-- Composition of residual translations. -/
def comp
    {E F G : Type u}
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F) : ResidualRefinement E G :=
  fun e => g (f e)

@[simp] theorem id_apply
    (E : Type u) (e : E) :
    id E e = e := by
  rfl

@[simp] theorem comp_apply
    {E F G : Type u}
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F)
    (e : E) :
    comp g f e = g (f e) := by
  rfl

@[simp] theorem comp_id
    {E F : Type u}
    (f : ResidualRefinement E F) :
    comp (id F) f = f := by
  rfl

@[simp] theorem id_comp
    {E F : Type u}
    (f : ResidualRefinement E F) :
    comp f (id E) = f := by
  rfl

@[simp] theorem comp_assoc
    {E F G H : Type u}
    (h : ResidualRefinement G H)
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F) :
    comp h (comp g f) = comp (comp h g) f := by
  rfl

/-- There is a canonical translation from every residual vocabulary to the
one-point vocabulary. -/
def toUnit (E : Type u) : ResidualRefinement E Unit :=
  fun _ => ()

/-- The translation to the one-point residual vocabulary is unique. -/
theorem toUnit_unique
    (E : Type u)
    (f : ResidualRefinement E Unit) :
    f = toUnit E := by
  funext e
  exact Subsingleton.elim _ _

end ResidualRefinement

namespace ResolutionAnswerWith

/-- Translate only the residual information of a Resolution Answer.  Realized
ordinary solutions are preserved literally. -/
def mapResidual
    {S : Specification.{u}}
    {E F : Type u}
    (f : ResidualRefinement E F) :
    ResolutionAnswerWith S E -> ResolutionAnswerWith S F
  | .realized x hx => .realized x hx
  | .residual e => .residual (f e)

@[simp] theorem mapResidual_realized
    {S : Specification.{u}}
    {E F : Type u}
    (f : ResidualRefinement E F)
    (x : S.Candidate)
    (hx : S.accepts x) :
    mapResidual f (.realized x hx : ResolutionAnswerWith S E) =
      (.realized x hx : ResolutionAnswerWith S F) := by
  rfl

@[simp] theorem mapResidual_residual
    {S : Specification.{u}}
    {E F : Type u}
    (f : ResidualRefinement E F)
    (e : E) :
    mapResidual f (.residual e : ResolutionAnswerWith S E) =
      (.residual (f e) : ResolutionAnswerWith S F) := by
  rfl

@[simp] theorem mapResidual_realize
    {S : Specification.{u}}
    {E F : Type u}
    (f : ResidualRefinement E F)
    (x : Specification.Solution S) :
    mapResidual f
        (ResolutionAnswerWith.realize x : ResolutionAnswerWith S E) =
      (ResolutionAnswerWith.realize x : ResolutionAnswerWith S F) := by
  cases x
  rfl

@[simp] theorem mapResidual_id
    {S : Specification.{u}}
    {E : Type u}
    (a : ResolutionAnswerWith S E) :
    mapResidual (ResidualRefinement.id E) a = a := by
  cases a <;> rfl

@[simp] theorem mapResidual_comp
    {S : Specification.{u}}
    {E F G : Type u}
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F)
    (a : ResolutionAnswerWith S E) :
    mapResidual (ResidualRefinement.comp g f) a =
      mapResidual g (mapResidual f a) := by
  cases a <;> rfl

/-- A bijective change of residual vocabulary induces an equivalence of the
corresponding Strong Totality answer types. -/
def mapResidualEquiv
    (S : Specification.{u})
    {E F : Type u}
    (e : Equiv E F) :
    Equiv (ResolutionAnswerWith S E) (ResolutionAnswerWith S F) where
  toFun := mapResidual e
  invFun := mapResidual e.symm
  left_inv := by
    intro a
    cases a with
    | realized x hx => rfl
    | residual r =>
        simp [mapResidual]
  right_inv := by
    intro a
    cases a with
    | realized x hx => rfl
    | residual r =>
        simp [mapResidual]

/-- `mapResidual` is the unique map that fixes ordinary solutions and translates
residuals by the specified residual refinement. -/
theorem mapResidual_unique
    (S : Specification.{u})
    {E F : Type u}
    (f : ResidualRefinement E F)
    (g : ResolutionAnswerWith S E -> ResolutionAnswerWith S F)
    (hSolution : forall x : Specification.Solution S,
      g (ResolutionAnswerWith.realize x) = ResolutionAnswerWith.realize x)
    (hResidual : forall e : E,
      g (.residual e) = (.residual (f e) : ResolutionAnswerWith S F)) :
    g = mapResidual f := by
  funext a
  cases a with
  | realized x hx =>
      have h := hSolution (⟨x, hx⟩ : Specification.Solution S)
      simpa [ResolutionAnswerWith.realize] using h
  | residual e =>
      exact hResidual e

end ResolutionAnswerWith

/-- Coarsening through the unique residual map `E -> Unit`, followed by the
canonical equivalence with the original one-residual semantics, is exactly the
existing provenance-forgetting map `coarsenResidual`. -/
theorem coarsenResidual_eq_terminalMap
    (S : Specification.{u})
    {E : Type u}
    (a : ResolutionAnswerWith S E) :
    unitResidualEquiv S
        (ResolutionAnswerWith.mapResidual
          (ResidualRefinement.toUnit E) a) =
      coarsenResidual a := by
  cases a <;> rfl

/-- The minimal Strong Totality semantics is terminal among residual semantics
for a fixed specification: there is exactly one map to it that preserves every
ordinary solution and sends every residual to the unique residual. -/
theorem minimalResidualSemantics_terminal
    (S : Specification.{u})
    (E : Type u) :
    Exists fun f : ResolutionAnswerWith S E -> ResolutionAnswer S =>
      ((forall x : Specification.Solution S,
          f (ResolutionAnswerWith.realize x) = realizeSolution x) ∧
        (forall e : E,
          f (.residual e) =
            (ResolutionAnswer.residual : ResolutionAnswer S))) ∧
      forall g : ResolutionAnswerWith S E -> ResolutionAnswer S,
        ((forall x : Specification.Solution S,
            g (ResolutionAnswerWith.realize x) = realizeSolution x) ∧
          (forall e : E,
            g (.residual e) =
              (ResolutionAnswer.residual : ResolutionAnswer S))) ->
        g = f := by
  refine ⟨coarsenResidual, ?_, ?_⟩
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
        simpa [ResolutionAnswerWith.realize, realizeSolution] using h
    | residual e =>
        exact hg.2 e

/-- Equivalent formulation: any two provenance-forgetting maps satisfying the
minimal Strong Totality equations are equal. -/
theorem minimalResidualCoarsening_unique
    (S : Specification.{u})
    {E : Type u}
    (f g : ResolutionAnswerWith S E -> ResolutionAnswer S)
    (hfSolution : forall x : Specification.Solution S,
      f (ResolutionAnswerWith.realize x) = realizeSolution x)
    (hfResidual : forall e : E,
      f (.residual e) =
        (ResolutionAnswer.residual : ResolutionAnswer S))
    (hgSolution : forall x : Specification.Solution S,
      g (ResolutionAnswerWith.realize x) = realizeSolution x)
    (hgResidual : forall e : E,
      g (.residual e) =
        (ResolutionAnswer.residual : ResolutionAnswer S)) :
    f = g := by
  rcases minimalResidualSemantics_terminal S E with ⟨terminal, _, huniq⟩
  have hf : f = terminal := huniq f ⟨hfSolution, hfResidual⟩
  have hg : g = terminal := huniq g ⟨hgSolution, hgResidual⟩
  exact hf.trans hg.symm

/-- The provenance-rich dependent semantics therefore has a unique canonical
map to the earlier single-residual dependent semantics. -/
theorem structuredDependent_to_minimal_terminal
    (S : Specification.{u})
    (T : Specification.Solution S -> Specification.{u}) :
    Exists fun f : StructuredDependentAnswer S T ->
        ResolutionAnswer (dependentSpecification S T) =>
      ((forall x : Specification.Solution (dependentSpecification S T),
          f (ResolutionAnswerWith.realize x) = realizeSolution x) ∧
        (forall e : DependentResidual S,
          f (.residual e) =
            (ResolutionAnswer.residual :
              ResolutionAnswer (dependentSpecification S T)))) ∧
      forall g : StructuredDependentAnswer S T ->
          ResolutionAnswer (dependentSpecification S T),
        ((forall x : Specification.Solution (dependentSpecification S T),
            g (ResolutionAnswerWith.realize x) = realizeSolution x) ∧
          (forall e : DependentResidual S,
            g (.residual e) =
              (ResolutionAnswer.residual :
                ResolutionAnswer (dependentSpecification S T)))) ->
        g = f :=
  minimalResidualSemantics_terminal
    (dependentSpecification S T) (DependentResidual S)

end StrongTotality
end Resolution
