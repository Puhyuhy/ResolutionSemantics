import ResolutionIntrinsicFiniteComplementPublic

/-!
# Public intrinsic finite-complement API

This facade exposes the intrinsic condition and its derived presentations under
stable publication-facing names.  The primitive budget is only an injection of
the genuine outside part into `Fin (n + 1)`.  The canonical finite-tag carrier
is derived from that condition; it is not built into the definition.
-/

universe u v w

namespace ResolutionSemantics

variable {Sigma : Resolution.Signature.{u}}

abbrev OutsideOld
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.TotalAlg.{u,v,w} D) :=
  Resolution.External.OutsideOld D T

noncomputable def oldOrOutsideEquiv
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.TotalAlg.{u,v,w} D) :
    Resolution.External.CarrierBijection
      T.Carrier (D.Carrier ⊕ OutsideOld D T) :=
  Resolution.External.oldOrOutsideEquiv D T

def outsideEquiv
    (D : Resolution.PartialAlg.{u,v} Sigma) (n : Nat)
    (T : Resolution.External.FiniteTagAlg D n) :
    Resolution.External.CarrierBijection
      (OutsideOld D (T.toTotalAlg D)) (Fin n ⊕ Unit) :=
  Resolution.External.outsideEquiv D n T

theorem intrinsicExtensionHasCanonicalPresentation
    {D : Resolution.PartialAlg.{u,v} Sigma} {n : Nat}
    (E : Resolution.External.IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    Exists fun code : E.toTotalAlg.Carrier ->
        Resolution.External.FiniteTagCarrier D n =>
      Function.Injective code ∧
      forall a : D.Carrier,
        code (E.toTotalAlg.embed a) =
          (Sum.inl a : Resolution.External.FiniteTagCarrier D n) :=
  Resolution.External.intrinsicExtensionHasCanonicalPresentation E

theorem qualitativeFiniteComplementSeparating_theorem
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Resolution.External.IntrinsicFiniteComplementSeparating D :=
  Resolution.External.qualitativeFiniteComplementSeparating_theorem D

end ResolutionSemantics
