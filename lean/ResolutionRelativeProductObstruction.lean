import ResolutionPropernessCriteriaComparison

/-!
# Relative finite-complement product obstruction

The standard way to combine finitely many residual separators is to take their
finite product.  For the observer class used by Resolution Semantics this
argument is not available when the pointwise-preserved base is infinite.

This module isolates the obstruction already at carrier level, before any
algebraic operations are considered.  A relative embedding has finite
complement when the points outside its image inject into some finite type.
The one-point extension `A -> A ⊕ Unit` has one-point complement for every
base `A`.  However, for `A = Nat`, the diagonal product of two such one-point
extensions has infinitely many mixed points `(a, star)` outside the diagonal
old image.  Hence the carrier-side finite-complement condition is not closed
under binary products.
-/

universe u v w

namespace ResolutionSemantics
namespace RelativeObservers

/-- Points outside the image of a distinguished base embedding.  This is the
carrier-level abstraction of `Resolution.External.OutsideOld`. -/
abbrev RelativeOutside
    {A : Type u} {T : Type v} (embed : A -> T) :=
  {z : T // forall a : A, z ≠ embed a}

/-- The carrier-side finite-complement property: all points outside the base
image inject into one finite type. -/
def HasFiniteRelativeComplement
    {A : Type u} {T : Type v} (embed : A -> T) : Prop :=
  Exists fun n : Nat =>
    Exists fun code : RelativeOutside embed -> Fin n =>
      Function.Injective code

/-- The canonical one-point extension of a carrier. -/
def onePointEmbedding (A : Type u) : A -> A ⊕ Unit :=
  fun a => Sum.inl a

/-- Product of two embeddings of the same distinguished base, using the
usual diagonal base map into the Cartesian product. -/
def binaryProductEmbedding
    {A : Type u} {T : Type v} {U : Type w}
    (left : A -> T) (right : A -> U) : A -> T × U :=
  fun a => (left a, right a)

private theorem onePointOutside_subsingleton
    (A : Type u)
    (x y : RelativeOutside (onePointEmbedding A)) : x = y := by
  apply Subtype.ext
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | inl a =>
      exact False.elim (hx a rfl)
  | inr ux =>
      cases ux
      cases y with
      | inl b =>
          exact False.elim (hy b rfl)
      | inr uy =>
          cases uy
          rfl

/-- A one-point extension has finite relative complement, independently of
whether the distinguished base itself is finite or infinite. -/
theorem onePointEmbedding_hasFiniteRelativeComplement
    (A : Type u) :
    HasFiniteRelativeComplement (onePointEmbedding A) := by
  refine ⟨1, (fun _ => (0 : Fin 1)), ?_⟩
  intro x y _
  exact onePointOutside_subsingleton A x y

/-- For the diagonal product of two one-point extensions, every base element
produces a mixed outside point `(a, star)`. -/
def natMixedOutside (a : Nat) :
    RelativeOutside
      (binaryProductEmbedding
        (onePointEmbedding Nat) (onePointEmbedding Nat)) :=
  ⟨(Sum.inl a, Sum.inr ()), by
    intro b h
    have hr := congrArg Prod.snd h
    cases hr⟩

/-- The mixed outside points retain the full natural-number parameter. -/
theorem natMixedOutside_injective :
    Function.Injective natMixedOutside := by
  intro a b h
  have hl : (Sum.inl a : Nat ⊕ Unit) = Sum.inl b :=
    congrArg
      (fun z : RelativeOutside
          (binaryProductEmbedding
            (onePointEmbedding Nat) (onePointEmbedding Nat)) => z.1.1)
      h
  exact Sum.inl.inj hl

/-- The diagonal product of two one-point relative extensions of `Nat` has no
finite relative complement. -/
theorem natOnePointProduct_hasNoFiniteRelativeComplement :
    ¬ HasFiniteRelativeComplement
      (binaryProductEmbedding
        (onePointEmbedding Nat) (onePointEmbedding Nat)) := by
  rintro ⟨n, code, hcode⟩
  let C : Resolution.Orbit.Coded Nat n := {
    code := fun a => (code (natMixedOutside a)).val
    code_lt := fun a => (code (natMixedOutside a)).isLt
    code_inj := by
      intro a b h
      apply natMixedOutside_injective
      apply hcode
      apply Fin.ext
      exact h
  }
  exact ResolutionSemantics.PropernessCriteria.natHasNoFiniteCode n ⟨C⟩

/-- Explicit failure of binary-product closure for the relative
finite-complement carrier condition.  Both factors separately have finite
complement, while their ordinary Cartesian product over the diagonal copy of
the infinite base does not. -/
theorem finiteRelativeComplement_not_closed_under_binary_products :
    HasFiniteRelativeComplement (onePointEmbedding Nat) ∧
    HasFiniteRelativeComplement (onePointEmbedding Nat) ∧
    ¬ HasFiniteRelativeComplement
      (binaryProductEmbedding
        (onePointEmbedding Nat) (onePointEmbedding Nat)) :=
  ⟨onePointEmbedding_hasFiniteRelativeComplement Nat,
    onePointEmbedding_hasFiniteRelativeComplement Nat,
    natOnePointProduct_hasNoFiniteRelativeComplement⟩

end RelativeObservers
end ResolutionSemantics
