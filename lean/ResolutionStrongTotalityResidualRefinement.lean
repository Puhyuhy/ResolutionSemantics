import ResolutionStrongTotalityResidualStructure

/-!
# Refinement and coarsening of residual semantics

Structured Strong Totality separates the existence of Resolution Answers from
how much information residual answers retain.  A map `E -> F` between residual
vocabularies is read from finer to coarser information: each residual datum in
`E` is translated into one in `F`.

Residual vocabularies may inhabit independent universes.  This is essential for
the terminal map to `Unit`, which lives in `Type 0`, and for kernel provenance,
whose natural universe need not coincide with that of mathematical candidates.
-/

universe u r s t

namespace Resolution
namespace StrongTotality

/-- A refinement/coarsening map between residual vocabularies. -/
abbrev ResidualRefinement (E : Type r) (F : Type s) : Type (max r s) := E -> F

namespace ResidualRefinement

/-- Identity residual translation. -/
def id (E : Type r) : ResidualRefinement E E := fun e => e

/-- Composition of residual translations. -/
def comp
    {E : Type r} {F : Type s} {G : Type t}
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F) : ResidualRefinement E G :=
  fun e => g (f e)

@[simp] theorem id_apply
    (E : Type r) (e : E) : id E e = e := by
  rfl

@[simp] theorem comp_apply
    {E : Type r} {F : Type s} {G : Type t}
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F)
    (e : E) : comp g f e = g (f e) := by
  rfl

@[simp] theorem comp_id
    {E : Type r} {F : Type s}
    (f : ResidualRefinement E F) :
    comp (id F) f = f := by
  rfl

@[simp] theorem id_comp
    {E : Type r} {F : Type s}
    (f : ResidualRefinement E F) :
    comp f (id E) = f := by
  rfl

@[simp] theorem comp_assoc
    {E : Type r} {F : Type s} {G : Type t} {H : Type u}
    (h : ResidualRefinement G H)
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F) :
    comp h (comp g f) = comp (comp h g) f := by
  rfl

/-- There is a canonical translation from every residual vocabulary to the
one-point vocabulary. -/
def toUnit (E : Type r) : ResidualRefinement E Unit :=
  fun _ => ()

/-- The translation to the one-point residual vocabulary is unique. -/
theorem toUnit_unique
    (E : Type r)
    (f : ResidualRefinement E Unit) :
    f = toUnit E := by
  funext e
  exact Subsingleton.elim _ _

end ResidualRefinement

namespace ResolutionAnswerWith

/-- Translate only residual information; realized solutions are preserved. -/
def mapResidual
    {S : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : ResidualRefinement E F) :
    ResolutionAnswerWith S E -> ResolutionAnswerWith S F
  | .realized x hx => .realized x hx
  | .residual e => .residual (f e)

@[simp] theorem mapResidual_realized
    {S : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : ResidualRefinement E F)
    (x : S.Candidate)
    (hx : S.accepts x) :
    mapResidual f (.realized x hx : ResolutionAnswerWith S E) =
      (.realized x hx : ResolutionAnswerWith S F) := by
  rfl

@[simp] theorem mapResidual_residual
    {S : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : ResidualRefinement E F)
    (e : E) :
    mapResidual f (.residual e : ResolutionAnswerWith S E) =
      (.residual (f e) : ResolutionAnswerWith S F) := by
  rfl

@[simp] theorem mapResidual_realize
    {S : Specification.{u}}
    {E : Type r} {F : Type s}
    (f : ResidualRefinement E F)
    (x : Specification.Solution S) :
    mapResidual f
        (ResolutionAnswerWith.realize x : ResolutionAnswerWith S E) =
      (ResolutionAnswerWith.realize x : ResolutionAnswerWith S F) := by
  cases x
  rfl

@[simp] theorem mapResidual_id
    {S : Specification.{u}}
    {E : Type r}
    (a : ResolutionAnswerWith S E) :
    mapResidual (ResidualRefinement.id E) a = a := by
  cases a <;> rfl

@[simp] theorem mapResidual_comp
    {S : Specification.{u}}
    {E : Type r} {F : Type s} {G : Type t}
    (g : ResidualRefinement F G)
    (f : ResidualRefinement E F)
    (a : ResolutionAnswerWith S E) :
    mapResidual (ResidualRefinement.comp g f) a =
      mapResidual g (mapResidual f a) := by
  cases a <;> rfl

/-- A bijective change of residual vocabulary induces an equivalence of answer
spaces. -/
def mapResidualEquiv
    (S : Specification.{u})
    {E : Type r} {F : Type s}
    (e : Equiv E F) :
    Equiv (ResolutionAnswerWith S E) (ResolutionAnswerWith S F) where
  toFun := mapResidual e
  invFun := mapResidual e.symm
  left_inv := by
    intro a
    cases a with
    | realized x hx => rfl
    | residual x =>
        change ResolutionAnswerWith.residual (e.invFun (e.toFun x)) =
          ResolutionAnswerWith.residual x
        rw [e.left_inv x]
  right_inv := by
    intro a
    cases a with
    | realized x hx => rfl
    | residual y =>
        change ResolutionAnswerWith.residual (e.toFun (e.invFun y)) =
          ResolutionAnswerWith.residual y
        rw [e.right_inv y]

/-- `mapResidual` is uniquely determined by its action on solutions and
residuals. -/
theorem mapResidual_unique
    (S : Specification.{u})
    {E : Type r} {F : Type s}
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
      exact hSolution (⟨x, hx⟩ : Specification.Solution S)
  | residual e =>
      exact hResidual e

end ResolutionAnswerWith

/-- Terminal coarsening agrees exactly with the original provenance-forgetting
map. -/
theorem coarsenResidual_eq_terminalMap
    (S : Specification.{u})
    {E : Type r}
    (a : ResolutionAnswerWith S E) :
    unitResidualEquiv S
        (ResolutionAnswerWith.mapResidual
          (ResidualRefinement.toUnit E) a) =
      coarsenResidual a := by
  cases a <;> rfl

/-- The minimal one-residual semantics is terminal for each fixed
specification. -/
theorem minimalResidualSemantics_terminal
    (S : Specification.{u})
    (E : Type r) :
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
        exact hg.1 (⟨x, hx⟩ : Specification.Solution S)
    | residual e =>
        exact hg.2 e

/-- Any two minimal provenance-forgetting maps satisfying the defining
equations coincide. -/
theorem minimalResidualCoarsening_unique
    (S : Specification.{u})
    {E : Type r}
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

/-- The provenance-rich dependent semantics has a unique canonical map to the
minimal dependent semantics. -/
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