import ResolutionStrongTotalityUniversalNaturality

/-!
# Representation invariance of Strong Totality

A foundational completion principle should depend on the mathematical problem,
not on an accidental encoding of that problem.  This module formalizes the
relevant notion of equivalence between specifications and proves that the
canonical Resolution completion preserves it.

A `SpecEquiv S T` consists of validity-preserving translations in both
directions whose underlying candidate maps are mutually inverse.  It therefore
identifies two representations of the same extensional solution problem.

Such an equivalence induces:

* equivalence of ordinary certified solution types;
* equivalence of minimal Resolution Answer types;
* mutually inverse universal completion maps;
* invariance of ordinary satisfiability.

Thus the Strong Totality completion is representation-invariant rather than a
construction tied to one syntactic presentation of a specification.
-/

universe u

namespace Resolution
namespace StrongTotality

/-- Equivalence of mathematical specifications by mutually inverse,
validity-preserving translations. -/
structure SpecEquiv (S T : Specification.{u}) where
  toMorphism : SpecMorphism S T
  invMorphism : SpecMorphism T S
  left_inv : forall x : S.Candidate,
    invMorphism.map (toMorphism.map x) = x
  right_inv : forall y : T.Candidate,
    toMorphism.map (invMorphism.map y) = y

namespace SpecEquiv

/-- Every specification is equivalent to itself. -/
def refl (S : Specification.{u}) : SpecEquiv S S where
  toMorphism := SpecMorphism.id S
  invMorphism := SpecMorphism.id S
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Reverse a specification equivalence. -/
def symm
    {S T : Specification.{u}}
    (e : SpecEquiv S T) : SpecEquiv T S where
  toMorphism := e.invMorphism
  invMorphism := e.toMorphism
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Compose specification equivalences. -/
def comp
    {S T U : Specification.{u}}
    (eTU : SpecEquiv T U)
    (eST : SpecEquiv S T) : SpecEquiv S U where
  toMorphism := SpecMorphism.comp eTU.toMorphism eST.toMorphism
  invMorphism := SpecMorphism.comp eST.invMorphism eTU.invMorphism
  left_inv := by
    intro x
    change eST.invMorphism.map
      (eTU.invMorphism.map
        (eTU.toMorphism.map (eST.toMorphism.map x))) = x
    rw [eTU.left_inv, eST.left_inv]
  right_inv := by
    intro z
    change eTU.toMorphism.map
      (eST.toMorphism.map
        (eST.invMorphism.map (eTU.invMorphism.map z))) = z
    rw [eST.right_inv, eTU.right_inv]

/-- Forward then backward transport of certified ordinary solutions is the
identity. -/
theorem mapSolution_left_inv
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (x : Specification.Solution S) :
    SpecMorphism.mapSolution e.invMorphism
        (SpecMorphism.mapSolution e.toMorphism x) = x := by
  cases x with
  | mk x hx =>
      cases e.left_inv x
      rfl

/-- Backward then forward transport of certified ordinary solutions is the
identity. -/
theorem mapSolution_right_inv
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (y : Specification.Solution T) :
    SpecMorphism.mapSolution e.toMorphism
        (SpecMorphism.mapSolution e.invMorphism y) = y := by
  cases y with
  | mk y hy =>
      cases e.right_inv y
      rfl

/-- Equivalent specifications have equivalent types of ordinary certified
solutions. -/
def solutionEquiv
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    Equiv (Specification.Solution S) (Specification.Solution T) where
  toFun := SpecMorphism.mapSolution e.toMorphism
  invFun := SpecMorphism.mapSolution e.invMorphism
  left_inv := mapSolution_left_inv e
  right_inv := mapSolution_right_inv e

/-- Equivalent specifications are ordinarily satisfiable simultaneously. -/
theorem satisfiable_iff
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    Specification.Satisfiable S ↔ Specification.Satisfiable T := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    exact ⟨e.toMorphism.map x, e.toMorphism.preserves x hx⟩
  · intro h
    rcases h with ⟨y, hy⟩
    exact ⟨e.invMorphism.map y, e.invMorphism.preserves y hy⟩

/-- Forward then backward transport of minimal Resolution Answers is the
identity. -/
theorem resolution_left_inv
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (a : ResolutionAnswer S) :
    ResolutionAnswer.map e.invMorphism
        (ResolutionAnswer.map e.toMorphism a) = a := by
  cases a with
  | residual => rfl
  | realized x hx =>
      cases e.left_inv x
      rfl

/-- Backward then forward transport of minimal Resolution Answers is the
identity. -/
theorem resolution_right_inv
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (a : ResolutionAnswer T) :
    ResolutionAnswer.map e.toMorphism
        (ResolutionAnswer.map e.invMorphism a) = a := by
  cases a with
  | residual => rfl
  | realized y hy =>
      cases e.right_inv y
      rfl

/-- The canonical Resolution completion preserves equivalence of mathematical
specifications. -/
def resolutionEquiv
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    Equiv (ResolutionAnswer S) (ResolutionAnswer T) where
  toFun := ResolutionAnswer.map e.toMorphism
  invFun := ResolutionAnswer.map e.invMorphism
  left_inv := resolution_left_inv e
  right_inv := resolution_right_inv e

/-- Representation invariance in completion language: equivalent
specifications have equivalent canonical completion carriers. -/
def canonicalCompletionEquiv
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    Equiv (canonicalCompletion S).Carrier (canonicalCompletion T).Carrier :=
  resolutionEquiv e

/-- The forward universal completion map of a specification equivalence is
invertible by the universal map of its inverse equivalence. -/
theorem canonicalCompletionEquiv_left
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (a : (canonicalCompletion S).Carrier) :
    (canonicalCompletionFunctorMap e.invMorphism).toFun
        ((canonicalCompletionFunctorMap e.toMorphism).toFun a) = a := by
  exact resolution_left_inv e a

/-- The other inverse law for canonical completion transport. -/
theorem canonicalCompletionEquiv_right
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (a : (canonicalCompletion T).Carrier) :
    (canonicalCompletionFunctorMap e.toMorphism).toFun
        ((canonicalCompletionFunctorMap e.invMorphism).toFun a) = a := by
  exact resolution_right_inv e a

/-- The completion equivalence fixes the distinguished residual answer. -/
@[simp] theorem canonicalCompletionEquiv_residual
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    (canonicalCompletionEquiv e).toFun
        (canonicalCompletion S).residual =
      (canonicalCompletion T).residual := by
  rfl

/-- The completion equivalence transports embedded ordinary solutions exactly
through the underlying specification equivalence. -/
@[simp] theorem canonicalCompletionEquiv_solution
    {S T : Specification.{u}}
    (e : SpecEquiv S T)
    (x : Specification.Solution S) :
    (canonicalCompletionEquiv e).toFun
        ((canonicalCompletion S).includeSolution x) =
      (canonicalCompletion T).includeSolution
        (SpecMorphism.mapSolution e.toMorphism x) := by
  exact ResolutionAnswer.map_realizeSolution e.toMorphism x

/-- Strong Totality itself is invariant under equivalent representation: a
Resolution Answer for either representation transports reversibly to the
other. -/
theorem strongTotality_representationInvariant
    {S T : Specification.{u}}
    (e : SpecEquiv S T) :
    Nonempty (Equiv (ResolutionAnswer S) (ResolutionAnswer T)) :=
  ⟨resolutionEquiv e⟩

end SpecEquiv
end StrongTotality
end Resolution
