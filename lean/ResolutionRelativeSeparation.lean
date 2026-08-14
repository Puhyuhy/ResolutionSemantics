import ResolutionSemanticsCompletion

/-!
# Canonical finite-tag presentations

The finite-tag carrier retains the old carrier pointwise and adds finitely many
charged states plus one overflow state.  This module packages extensions that
come equipped with explicit mutually inverse maps to that canonical carrier.

This is a useful transport normal form, but it is not the intrinsic definition
of finite complement.  The intrinsic condition and its representation theorem
are developed in `ResolutionIntrinsicFiniteComplement.lean`.
-/

universe u v w

namespace Resolution
namespace External

variable {Sigma : Signature.{u}}

/-- A small local replacement for an equivalence, expressed only through
    functions and inverse laws. -/
structure CarrierBijection (α : Type w) (β : Type v) where
  toFun : α -> β
  invFun : β -> α
  left_inv : forall x : α, invFun (toFun x) = x
  right_inv : forall y : β, toFun (invFun y) = y

namespace CarrierBijection

variable {α : Type w} {β : Type v}

theorem toFun_injective
    (e : CarrierBijection α β) : Function.Injective e.toFun := by
  intro x y hxy
  calc
    x = e.invFun (e.toFun x) := (e.left_inv x).symm
    _ = e.invFun (e.toFun y) := congrArg e.invFun hxy
    _ = y := e.left_inv y

end CarrierBijection

/-- A compatible total extension supplied with a base-fixing canonical
    finite-tag presentation. -/
structure FiniteComplementExtension
    (D : PartialAlg.{u,v} Sigma) (n : Nat) where
  toTotalAlg : Free.TotalAlg.{u,v,w} D
  carrierPresentation :
    CarrierBijection toTotalAlg.Carrier (FiniteTagCarrier D n)
  carrierPresentation_embed : forall a : D.Carrier,
    carrierPresentation.toFun (toTotalAlg.embed a) =
      (Sum.inl a : FiniteTagCarrier D n)

namespace FiniteComplementExtension

variable {D : PartialAlg.{u,v} Sigma} {n : Nat}

/-- The inverse presentation map sends each old point back to the old
    embedding. -/
theorem carrierPresentation_inv_old
    (E : FiniteComplementExtension.{u,v,w} D n)
    (a : D.Carrier) :
    E.carrierPresentation.invFun
        (Sum.inl a : FiniteTagCarrier D n) =
      E.toTotalAlg.embed a := by
  apply CarrierBijection.toFun_injective E.carrierPresentation
  calc
    E.carrierPresentation.toFun
        (E.carrierPresentation.invFun
          (Sum.inl a : FiniteTagCarrier D n)) =
        (Sum.inl a : FiniteTagCarrier D n) :=
      E.carrierPresentation.right_inv _
    _ = E.carrierPresentation.toFun (E.toTotalAlg.embed a) :=
      (E.carrierPresentation_embed a).symm

/-- Transport a canonical-presentation extension to a finite-tag algebra. -/
def toFiniteTagAlg
    (E : FiniteComplementExtension.{u,v,w} D n) :
    FiniteTagAlg D n where
  op := fun f x y =>
    E.carrierPresentation.toFun
      (E.toTotalAlg.op f
        (E.carrierPresentation.invFun x)
        (E.carrierPresentation.invFun y))
  preserve := by
    intro f a b c h
    change E.carrierPresentation.toFun
      (E.toTotalAlg.op f
        (E.carrierPresentation.invFun (Sum.inl a))
        (E.carrierPresentation.invFun (Sum.inl b))) = Sum.inl c
    rw [carrierPresentation_inv_old E a,
      carrierPresentation_inv_old E b]
    rw [E.toTotalAlg.preserve f a b c h]
    exact E.carrierPresentation_embed c

/-- Every concrete finite-tag algebra has the canonical presentation. -/
def ofFiniteTagAlg
    (T : FiniteTagAlg D n) :
    FiniteComplementExtension.{u,v,v} D n where
  toTotalAlg := T.toTotalAlg D
  carrierPresentation := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  carrierPresentation_embed := by
    intro a
    rfl

/-- Folding commutes with transport to the canonical carrier. -/
theorem foldRaw_toFiniteTagAlg
    (E : FiniteComplementExtension.{u,v,w} D n) :
    forall t : RawAns Sigma D.Carrier,
      E.carrierPresentation.toFun
          (Free.TotalAlg.foldRaw D E.toTotalAlg t) =
        Free.TotalAlg.foldRaw D
          ((E.toFiniteTagAlg).toTotalAlg D) t
  | .old a => E.carrierPresentation_embed a
  | .susp f x y => by
      simp only [Free.TotalAlg.foldRaw]
      change E.carrierPresentation.toFun
          (E.toTotalAlg.op f
            (Free.TotalAlg.foldRaw D E.toTotalAlg x)
            (Free.TotalAlg.foldRaw D E.toTotalAlg y)) =
        E.carrierPresentation.toFun
          (E.toTotalAlg.op f
            (E.carrierPresentation.invFun
              (Free.TotalAlg.foldRaw D
                ((E.toFiniteTagAlg).toTotalAlg D) x))
            (E.carrierPresentation.invFun
              (Free.TotalAlg.foldRaw D
                ((E.toFiniteTagAlg).toTotalAlg D) y)))
      rw [← foldRaw_toFiniteTagAlg E x,
        ← foldRaw_toFiniteTagAlg E y]
      rw [E.carrierPresentation.left_inv,
        E.carrierPresentation.left_inv]

/-- Generated interpretation commutes with transport. -/
theorem interp_toFiniteTagAlg
    (E : FiniteComplementExtension.{u,v,w} D n)
    (x : Free.GeneratedAns D) :
    E.carrierPresentation.toFun
        (Free.TotalAlg.interp D E.toTotalAlg x) =
      Free.TotalAlg.interp D
        ((E.toFiniteTagAlg).toTotalAlg D) x :=
  foldRaw_toFiniteTagAlg E x.1

end FiniteComplementExtension

/-- Pairwise separation by an extension carrying the canonical finite-tag
    presentation. -/
def FiniteComplementSeparatesAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (n : Nat) : Prop :=
  Exists fun E : FiniteComplementExtension.{u,v,v} D n =>
    Free.TotalAlg.interp D E.toTotalAlg x ≠
      Free.TotalAlg.interp D E.toTotalAlg y

/-- Canonical-presentation separation and finite-tag separation are equivalent
    by transport.  This theorem is intentionally not presented as the
    intrinsic finite-complement result. -/
theorem finiteComplementSeparatesAt_iff_finiteTagSeparatesAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (n : Nat) :
    FiniteComplementSeparatesAt D x y n <->
      FiniteTagSeparatesAt D x y n := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨E.toFiniteTagAlg, ?_⟩
    intro hEq
    apply hE
    apply CarrierBijection.toFun_injective E.carrierPresentation
    rw [E.interp_toFiniteTagAlg x,
      E.interp_toFiniteTagAlg y]
    exact hEq
  · rintro ⟨T, hT⟩
    exact ⟨FiniteComplementExtension.ofFiniteTagAlg T, hT⟩

/-- The constructor-count separator also has the canonical presentation. -/
theorem finiteComplementSeparatesAt_size_bound
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (hxy : x ≠ y) :
    FiniteComplementSeparatesAt D x y
      (FiniteTagProof.nodeCount D x.1 +
        FiniteTagProof.nodeCount D y.1) :=
  (finiteComplementSeparatesAt_iff_finiteTagSeparatesAt D x y _).2
    (finiteTagSeparatesAt_size_bound D x y hxy)

end External
end Resolution
