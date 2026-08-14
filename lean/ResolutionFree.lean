import ResolutionKernel

universe u v w

namespace Resolution
namespace Free

variable {Sigma : Signature.{u}}

def GeneratedAns (D : PartialAlg.{u,v} Sigma) : Type (max u v) :=
  {a : RawAns Sigma D.Carrier //
    Exists fun e : Expr Sigma D.Carrier => Expr.res D e = a}

structure TotalAlg (D : PartialAlg.{u,v} Sigma) where
  Carrier : Type w
  embed : D.Carrier -> Carrier
  embed_injective : Function.Injective embed
  op : Sigma.Op -> Carrier -> Carrier -> Carrier
  preserve : forall (f : Sigma.Op) (a b c : D.Carrier),
    D.eval f a b = some c -> op f (embed a) (embed b) = embed c

namespace TotalAlg

variable (D : PartialAlg.{u,v} Sigma) (T : TotalAlg D)

def foldRaw : RawAns Sigma D.Carrier -> T.Carrier
  | .old a => T.embed a
  | .susp f x y => T.op f (foldRaw x) (foldRaw y)

def interp (x : GeneratedAns D) : T.Carrier :=
  foldRaw D T x.1

end TotalAlg
end Free
end Resolution
