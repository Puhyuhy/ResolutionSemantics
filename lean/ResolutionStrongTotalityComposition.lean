import ResolutionStrongTotalityFunctorial

/-!
# Compositional Strong Totality

The universal Resolution completion should remain total under sequential use.
This module gives Resolution Answers their canonical Kleisli-style composition:
a realized solution may feed a subsequent Resolution computation, while a
residual propagates without being mistaken for a realized solution.

The resulting arrows compose associatively with realized solutions as units.
Moreover, ordinary partial arrows embed compositionally into Resolution arrows.
Thus Strong Totality is closed under sequential construction of mathematical
problems rather than being only a pointwise existence statement.
-/

universe u

namespace Resolution
namespace StrongTotality

namespace ResolutionAnswer

/-- Sequentially continue from a Resolution Answer.  A realized solution is
passed to the continuation; an unresolved source remains unresolved. -/
def bind
    {S T : Specification.{u}}
    (a : ResolutionAnswer S)
    (k : Specification.Solution S -> ResolutionAnswer T) :
    ResolutionAnswer T :=
  match a with
  | .realized x hx => k ⟨x, hx⟩
  | .residual => .residual

@[simp] theorem bind_realized
    {S T : Specification.{u}}
    (x : S.Candidate)
    (hx : S.accepts x)
    (k : Specification.Solution S -> ResolutionAnswer T) :
    bind (.realized x hx) k = k ⟨x, hx⟩ := by
  rfl

@[simp] theorem bind_residual
    {S T : Specification.{u}}
    (k : Specification.Solution S -> ResolutionAnswer T) :
    bind (ResolutionAnswer.residual : ResolutionAnswer S) k = .residual := by
  rfl

/-- Left unit: an already-realized ordinary solution can immediately be used by
the next Resolution computation. -/
@[simp] theorem bind_realizeSolution
    {S T : Specification.{u}}
    (x : Specification.Solution S)
    (k : Specification.Solution S -> ResolutionAnswer T) :
    bind (realizeSolution x) k = k x := by
  cases x
  rfl

/-- Right unit: asking only to re-embed an answer does not change it. -/
@[simp] theorem bind_right_identity
    {S : Specification.{u}}
    (a : ResolutionAnswer S) :
    bind a (fun x => realizeSolution x) = a := by
  cases a <;> rfl

/-- Sequential Resolution is associative. -/
theorem bind_assoc
    {S T U : Specification.{u}}
    (a : ResolutionAnswer S)
    (f : Specification.Solution S -> ResolutionAnswer T)
    (g : Specification.Solution T -> ResolutionAnswer U) :
    bind (bind a f) g = bind a (fun x => bind (f x) g) := by
  cases a <;> rfl

/-- The functorial map from specification morphisms is the special case of
`bind` in which the continuation always returns a realized translated
solution. -/
theorem map_eq_bind
    {S T : Specification.{u}}
    (f : SpecMorphism S T)
    (a : ResolutionAnswer S) :
    ResolutionAnswer.map f a =
      bind a (fun x => realizeSolution (SpecMorphism.mapSolution f x)) := by
  cases a <;> rfl

end ResolutionAnswer

/-! ## Resolution arrows -/

/-- A Resolution arrow may use an ordinary solution of `S` to produce a total
Resolution Answer for `T`. -/
def ResolutionArrow (S T : Specification.{u}) : Type u :=
  Specification.Solution S -> ResolutionAnswer T

namespace ResolutionArrow

/-- Identity Resolution arrow. -/
def id (S : Specification.{u}) : ResolutionArrow S S :=
  fun x => realizeSolution x

/-- Sequential composition of Resolution arrows. -/
def comp
    {S T U : Specification.{u}}
    (g : ResolutionArrow T U)
    (f : ResolutionArrow S T) : ResolutionArrow S U :=
  fun x => ResolutionAnswer.bind (f x) g

@[simp] theorem comp_id
    {S T : Specification.{u}}
    (f : ResolutionArrow S T) :
    comp (id T) f = f := by
  funext x
  exact ResolutionAnswer.bind_right_identity (f x)

@[simp] theorem id_comp
    {S T : Specification.{u}}
    (f : ResolutionArrow S T) :
    comp f (id S) = f := by
  funext x
  rfl

@[simp] theorem comp_assoc
    {S T U V : Specification.{u}}
    (h : ResolutionArrow U V)
    (g : ResolutionArrow T U)
    (f : ResolutionArrow S T) :
    comp h (comp g f) = comp (comp h g) f := by
  funext x
  exact ResolutionAnswer.bind_assoc (f x) g h

/-- Every validity-preserving specification morphism determines a Resolution
arrow that never introduces a residual on realized input. -/
def ofMorphism
    {S T : Specification.{u}}
    (f : SpecMorphism S T) : ResolutionArrow S T :=
  fun x => realizeSolution (SpecMorphism.mapSolution f x)

@[simp] theorem ofMorphism_id
    (S : Specification.{u}) :
    ofMorphism (SpecMorphism.id S) = id S := by
  rfl

@[simp] theorem ofMorphism_comp
    {S T U : Specification.{u}}
    (g : SpecMorphism T U)
    (f : SpecMorphism S T) :
    ofMorphism (SpecMorphism.comp g f) = comp (ofMorphism g) (ofMorphism f) := by
  funext x
  cases x
  rfl

end ResolutionArrow

/-! ## Ordinary partial arrows embed compositionally -/

/-- An ordinary partial mathematical arrow. -/
def PartialArrow (S T : Specification.{u}) : Type u :=
  Specification.Solution S -> Option (Specification.Solution T)

namespace PartialArrow

/-- Identity partial arrow. -/
def id (S : Specification.{u}) : PartialArrow S S :=
  fun x => some x

/-- Sequential composition of ordinary partial arrows. -/
def comp
    {S T U : Specification.{u}}
    (g : PartialArrow T U)
    (f : PartialArrow S T) : PartialArrow S U :=
  fun x =>
    match f x with
    | some y => g y
    | none => none

end PartialArrow

/-- Canonically totalize an ordinary partial arrow into a Resolution arrow. -/
def totalizePartialArrow
    {S T : Specification.{u}}
    (f : PartialArrow S T) : ResolutionArrow S T :=
  fun x => totalize T (f x)

@[simp] theorem totalizePartialArrow_id
    (S : Specification.{u}) :
    totalizePartialArrow (PartialArrow.id S) = ResolutionArrow.id S := by
  rfl

/-- Canonical totalization preserves sequential composition exactly. -/
theorem totalizePartialArrow_comp
    {S T U : Specification.{u}}
    (g : PartialArrow T U)
    (f : PartialArrow S T) :
    totalizePartialArrow (PartialArrow.comp g f) =
      ResolutionArrow.comp (totalizePartialArrow g) (totalizePartialArrow f) := by
  funext x
  cases h : f x with
  | none =>
      simp [totalizePartialArrow, PartialArrow.comp, ResolutionArrow.comp,
        ResolutionAnswer.bind, totalize, h]
  | some y =>
      simp [totalizePartialArrow, PartialArrow.comp, ResolutionArrow.comp,
        ResolutionAnswer.bind, totalize, h]

/-- Strong Totality is therefore closed under any finite two-stage partial
mathematical computation: compose first in the partial world or totalize each
stage first; the resulting Resolution computation is identical. -/
theorem strongTotality_compositional
    {S T U : Specification.{u}}
    (f : PartialArrow S T)
    (g : PartialArrow T U) :
    totalizePartialArrow (PartialArrow.comp g f) =
      ResolutionArrow.comp (totalizePartialArrow g) (totalizePartialArrow f) :=
  totalizePartialArrow_comp g f

end StrongTotality
end Resolution
