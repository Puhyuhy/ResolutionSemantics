/-!
# Minimal type equivalence

The repository intentionally keeps a very small Lean dependency footprint.
The core imports used by the paper do not expose Lean's standard `Equiv`
declaration, while the Strong Totality research needs only the elementary
notion of a pair of mutually inverse maps.

This local declaration supplies exactly that structure and nothing more.  It
lives inside `Resolution.StrongTotality`, so it does not pollute the global
namespace or commit the project to an external category/equivalence library.
-/

universe u v

namespace Resolution
namespace StrongTotality

/-- A dependency-free equivalence between two types/sorts. -/
structure Equiv (A : Sort u) (B : Sort v) where
  toFun : A -> B
  invFun : B -> A
  left_inv : forall a : A, invFun (toFun a) = a
  right_inv : forall b : B, toFun (invFun b) = b

namespace Equiv

/-- Reverse a type equivalence. -/
def symm
    {A : Sort u} {B : Sort v}
    (e : Equiv A B) : Equiv B A where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Use an equivalence as its forward map. -/
instance
    {A : Sort u} {B : Sort v} :
    CoeFun (Equiv A B) (fun _ => A -> B) where
  coe := Equiv.toFun

@[simp] theorem symm_toFun
    {A : Sort u} {B : Sort v}
    (e : Equiv A B)
    (b : B) :
    e.symm b = e.invFun b := by
  rfl

end Equiv
end StrongTotality
end Resolution
