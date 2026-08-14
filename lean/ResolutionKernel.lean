import Std

universe u v

namespace Resolution

structure Signature where
  Op : Type u

structure PartialAlg (Sigma : Signature.{u}) where
  Carrier : Type v
  eval : Sigma.Op -> Carrier -> Carrier -> Option Carrier

inductive Expr (Sigma : Signature.{u}) (A : Type v) where
  | val : A -> Expr Sigma A
  | app : Sigma.Op -> Expr Sigma A -> Expr Sigma A -> Expr Sigma A

inductive RawAns (Sigma : Signature.{u}) (A : Type v) where
  | old : A -> RawAns Sigma A
  | susp : Sigma.Op -> RawAns Sigma A -> RawAns Sigma A -> RawAns Sigma A

namespace PartialAlg

variable {Sigma : Signature.{u}}

def liftOp (D : PartialAlg Sigma) (op : Sigma.Op)
    (x y : RawAns Sigma D.Carrier) : RawAns Sigma D.Carrier :=
  match x, y with
  | .old a, .old b =>
      match D.eval op a b with
      | some c => .old c
      | none => .susp op x y
  | _, _ => .susp op x y

end PartialAlg

namespace Expr

variable {Sigma : Signature.{u}}

def res (D : PartialAlg Sigma) : Expr Sigma D.Carrier -> RawAns Sigma D.Carrier
  | .val a => .old a
  | .app op left right => D.liftOp op (res D left) (res D right)

end Expr

end Resolution
