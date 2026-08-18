import ResolutionFree

/-!
# Strong Totality for arbitrary mathematical specifications

This module formalizes the intended Strong Totality principle itself, rather
than merely the already-total syntax evaluator `Expr.res`.

A *well-formed mathematical specification* is represented extensionally by a
type of candidate answers together with a predicate saying which candidates
satisfy the specification.  Well-formedness is therefore enforced by the type
system: an inhabitant of `Specification` is already a typed mathematical
specification.

The crucial distinction is between an ordinary solution and a Resolution
Answer.  An arbitrary specification need not possess an ordinary satisfying
candidate (the specification `False` is the simplest example).  Strong
Totality therefore cannot consistently mean that every specification has an
ordinary solution.  Instead the Resolution completion adjoins a residual
answer which retains the unresolved specification when no ordinary answer has
been supplied.

This gives the universal form of the principle:

  every well-formed specification has a Resolution Answer.

More strongly, every partial resolver of an arbitrary family of specifications
extends canonically to a total Resolution resolver: existing ordinary answers
are preserved, while missing answers become residuals.  This construction is
constructive; a separate classical theorem below shows how excluded middle can
refine a specification to either a realized answer or a proof that no ordinary
solution exists.
-/

universe u v

namespace Resolution
namespace StrongTotality

/-- A typed mathematical specification.  `Candidate` is the type in which an
ordinary answer would live and `accepts` is the condition that such an answer
must satisfy. -/
structure Specification where
  Candidate : Type u
  accepts : Candidate -> Prop

namespace Specification

/-- The type of ordinary solutions of a specification. -/
def Solution (S : Specification.{u}) : Type u :=
  {x : S.Candidate // S.accepts x}

/-- A specification is ordinarily satisfiable when it has a satisfying
candidate. -/
def Satisfiable (S : Specification.{u}) : Prop :=
  Exists fun x : S.Candidate => S.accepts x

end Specification

/-- A Resolution Answer either realizes the specification by an ordinary
solution or retains the specification as a residual.  The specification itself
is preserved by the index `S`; `residual` is therefore not an untyped failure
value. -/
inductive ResolutionAnswer (S : Specification.{u}) : Type u where
  | realized (x : S.Candidate) (hx : S.accepts x)
  | residual

/-- Forget a Resolution Answer back to an optional ordinary solution. -/
def ResolutionAnswer.solution?
    {S : Specification.{u}} :
    ResolutionAnswer S -> Option (Specification.Solution S)
  | .realized x hx => some ⟨x, hx⟩
  | .residual => none

/-- Totalize one partial attempt to solve `S`.  Existing solutions are kept
verbatim; absence of an ordinary answer becomes the residual Resolution
Answer. -/
def totalize
    (S : Specification.{u}) :
    Option (Specification.Solution S) -> ResolutionAnswer S
  | some x => .realized x.1 x.2
  | none => .residual

@[simp] theorem totalize_some
    (S : Specification.{u})
    (x : Specification.Solution S) :
    totalize S (some x) = .realized x.1 x.2 := by
  rfl

@[simp] theorem totalize_none
    (S : Specification.{u}) :
    totalize S none = .residual := by
  rfl

@[simp] theorem solution?_totalize_some
    (S : Specification.{u})
    (x : Specification.Solution S) :
    (totalize S (some x)).solution? = some x := by
  rfl

@[simp] theorem solution?_totalize_none
    (S : Specification.{u}) :
    (totalize S none).solution? = none := by
  rfl

/-- **Strong Totality.** Every well-formed mathematical specification has a
Resolution Answer.  This theorem is constructive: no decidability or excluded
middle is required because a genuinely unresolved specification is itself
retained as a typed residual answer. -/
theorem strongTotality
    (S : Specification.{u}) :
    Nonempty (ResolutionAnswer S) := by
  exact ⟨.residual⟩

/-! ## Families of arbitrary specifications -/

/-- A partial resolver for a family of specifications.  It may return an
ordinary satisfying answer or fail to provide one. -/
def PartialResolver
    {I : Type v}
    (F : I -> Specification.{u}) : Type (max u v) :=
  (i : I) -> Option (Specification.Solution (F i))

/-- A total Resolution resolver for a family of specifications. -/
def Resolver
    {I : Type v}
    (F : I -> Specification.{u}) : Type (max u v) :=
  (i : I) -> ResolutionAnswer (F i)

/-- Canonical pointwise extension of every partial resolver to a total
Resolution resolver. -/
def totalizeResolver
    {I : Type v}
    (F : I -> Specification.{u})
    (r : PartialResolver F) : Resolver F :=
  fun i => totalize (F i) (r i)

@[simp] theorem totalizeResolver_some
    {I : Type v}
    (F : I -> Specification.{u})
    (r : PartialResolver F)
    (i : I)
    (x : Specification.Solution (F i))
    (h : r i = some x) :
    totalizeResolver F r i = .realized x.1 x.2 := by
  simp [totalizeResolver, h]

@[simp] theorem totalizeResolver_none
    {I : Type v}
    (F : I -> Specification.{u})
    (r : PartialResolver F)
    (i : I)
    (h : r i = none) :
    totalizeResolver F r i = .residual := by
  simp [totalizeResolver, h]

/-- Family form of Strong Totality: every partial resolver, over an arbitrary
index type and arbitrary well-formed specifications, has a total Resolution
extension. -/
theorem strongTotality_extension
    {I : Type v}
    (F : I -> Specification.{u})
    (r : PartialResolver F) :
    Exists fun R : Resolver F =>
      forall i : I,
        R i = totalize (F i) (r i) := by
  exact ⟨totalizeResolver F r, fun _ => rfl⟩

/-! ## Arbitrary mathematical operations as specification families -/

/-- A dependent mathematical operation specification is just a family of
candidate output types with a relation specifying acceptable outputs.  This
covers ordinary functions, partial functions, relations, equations, search
problems, and dependent output problems. -/
def operationSpecification
    {I : Type v}
    {O : I -> Type u}
    (R : (i : I) -> O i -> Prop)
    (i : I) : Specification.{u} where
  Candidate := O i
  accepts := R i

/-- Every input of every well-formed dependent operation specification has a
Resolution Answer. -/
theorem operationStrongTotality
    {I : Type v}
    {O : I -> Type u}
    (R : (i : I) -> O i -> Prop)
    (i : I) :
    Nonempty (ResolutionAnswer (operationSpecification R i)) :=
  strongTotality (operationSpecification R i)

/-- Any partial implementation of a mathematical operation extends canonically
to a total Resolution-valued implementation. -/
def totalizeOperation
    {I : Type v}
    {O : I -> Type u}
    (R : (i : I) -> O i -> Prop)
    (r : (i : I) -> Option {y : O i // R i y}) :
    (i : I) -> ResolutionAnswer (operationSpecification R i) :=
  fun i => totalize (operationSpecification R i) (r i)

/-! ## Propositions are specifications too -/

/-- Embed an arbitrary proposition as a specification with one possible
candidate.  If the proposition is not presently realized, its Resolution
Answer can remain residual rather than becoming undefined. -/
def propositionSpecification (P : Prop) : Specification.{0} where
  Candidate := Unit
  accepts := fun _ => P

/-- Strong Totality therefore applies uniformly even to arbitrary propositions;
it does not require that the proposition be decidable. -/
theorem propositionStrongTotality
    (P : Prop) :
    Nonempty (ResolutionAnswer (propositionSpecification P)) :=
  strongTotality (propositionSpecification P)

/-! ## Classical decisiveness is a refinement, not the foundation -/

/-- If one additionally wants a decisive extensional verdict, classical logic
can replace the residual by either an ordinary realization or a proof that no
ordinary solution exists.  This is deliberately separated from constructive
Strong Totality above. -/
inductive DecisiveResolutionAnswer (S : Specification.{u}) : Type u where
  | realized (x : S.Candidate) (hx : S.accepts x)
  | impossible (h : Not (Specification.Satisfiable S))

/-- Classical refinement: every specification is either realized or proved to
have no ordinary solution.  Unlike `strongTotality`, this theorem uses excluded
middle and should not be confused with the foundational Resolution principle. -/
theorem decisiveStrongTotality
    (S : Specification.{u}) :
    Nonempty (DecisiveResolutionAnswer S) := by
  classical
  by_cases h : Specification.Satisfiable S
  · rcases h with ⟨x, hx⟩
    exact ⟨.realized x hx⟩
  · exact ⟨.impossible h⟩

end StrongTotality
end Resolution
