import ResolutionModels

universe u v w

namespace Resolution
namespace External

variable {Sigma : Signature.{u}}

abbrev ModelFamily (D : PartialAlg Sigma) (I : Type w) :=
  I -> Free.TotalAlg D

def evalMap (D : PartialAlg Sigma) {I : Type w}
    (M : ModelFamily D I) (x : Free.GeneratedAns D) :
    (i : I) -> (M i).Carrier :=
  fun i => Free.TotalAlg.interp D (M i) x

def ModelEq (D : PartialAlg Sigma) {I : Type w}
    (M : ModelFamily D I) (x y : Free.GeneratedAns D) : Prop :=
  forall i : I, Free.TotalAlg.interp D (M i) x =
    Free.TotalAlg.interp D (M i) y

def JointlySeparating (D : PartialAlg Sigma) {I : Type w}
    (M : ModelFamily D I) : Prop :=
  forall {x y : Free.GeneratedAns D}, ModelEq D M x y -> x = y

theorem jointlySeparating_iff_evalMap_injective (D : PartialAlg Sigma)
    {I : Type w} (M : ModelFamily D I) :
    JointlySeparating D M <-> Function.Injective (evalMap D M) := by
  constructor
  · intro h x y hxy
    apply h
    intro i
    exact congrFun hxy i
  · intro h x y hxy
    apply h
    funext i
    exact hxy i

theorem modelEq_iff_eq_of_jointlySeparating (D : PartialAlg Sigma)
    {I : Type w} (M : ModelFamily D I) (hsep : JointlySeparating D M)
    (x y : Free.GeneratedAns D) :
    ModelEq D M x y <-> x = y := by
  constructor
  · exact hsep
  · intro h
    cases h
    intro i
    rfl

abbrev FiniteTagCarrier (D : PartialAlg Sigma) (n : Nat) :=
  Sum D.Carrier (Sum (Fin n) Unit)

structure FiniteTagAlg (D : PartialAlg Sigma) (n : Nat) where
  op : Sigma.Op -> FiniteTagCarrier D n -> FiniteTagCarrier D n ->
    FiniteTagCarrier D n
  preserve : forall (f : Sigma.Op) (a b c : D.Carrier),
    D.eval f a b = some c ->
      op f (Sum.inl a) (Sum.inl b) = Sum.inl c

namespace FiniteTagAlg

variable (D : PartialAlg Sigma) {n : Nat}

abbrev toTotalAlg (T : FiniteTagAlg D n) : Free.TotalAlg D where
  Carrier := FiniteTagCarrier D n
  embed := Sum.inl
  embed_injective := by
    intro a b h
    exact Sum.inl.inj h
  op := T.op
  preserve := T.preserve

end FiniteTagAlg

def FiniteTagEq (D : PartialAlg Sigma)
    (x y : Free.GeneratedAns D) : Prop :=
  forall (n : Nat) (T : FiniteTagAlg D n),
    Free.TotalAlg.interp D (T.toTotalAlg D) x =
      Free.TotalAlg.interp D (T.toTotalAlg D) y

theorem eq_implies_finiteTagEq (D : PartialAlg Sigma)
    {x y : Free.GeneratedAns D} (h : x = y) :
    FiniteTagEq D x y := by
  cases h
  intro n T
  rfl

def FiniteTagSeparating (D : PartialAlg Sigma) : Prop :=
  forall {x y : Free.GeneratedAns D}, FiniteTagEq D x y -> x = y

theorem finiteTag_full_abstraction (D : PartialAlg Sigma)
    (hsep : FiniteTagSeparating D) (x y : Free.GeneratedAns D) :
    FiniteTagEq D x y <-> x = y := by
  constructor
  · exact hsep
  · exact eq_implies_finiteTagEq D

end External
end Resolution
