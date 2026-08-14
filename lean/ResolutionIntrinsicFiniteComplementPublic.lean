import ResolutionIntrinsicFiniteComplement

universe u v

namespace ResolutionSemantics

variable {Sigma : Resolution.Signature.{u}}

abbrev IntrinsicOldComplement
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.TotalAlg D) :=
  Resolution.External.OldComplement D T

abbrev IntrinsicComplementBudget
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.TotalAlg D)
    (n : Nat) :=
  Resolution.External.ComplementBudget D T n

abbrev IntrinsicFiniteComplementExtension
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (n : Nat) :=
  Resolution.External.IntrinsicFiniteComplementExtension D n

abbrev IntrinsicFiniteComplementSeparating
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.External.IntrinsicFiniteComplementSeparating D

theorem intrinsicFiniteComplementSeparation
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    IntrinsicFiniteComplementSeparating D :=
  Resolution.External.intrinsicFiniteComplementSeparating_theorem D

theorem intrinsicSeparationIffFiniteTag
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (x y : Resolution.Free.GeneratedAns D) (n : Nat) :
    Resolution.External.IntrinsicFiniteComplementSeparatesAt D x y n ↔
      Resolution.External.FiniteTagSeparatesAt D x y n :=
  Resolution.External.intrinsicFiniteComplementSeparatesAt_iff_finiteTagSeparatesAt
    D x y n

end ResolutionSemantics
