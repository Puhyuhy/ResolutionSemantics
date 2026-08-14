import ResolutionFreeCompletionFinal
import ResolutionIntegerArithmetic

universe u v w q

/- Publication-facing API for the Resolution Semantics paper. -/
namespace ResolutionSemantics

variable {Sigma : Resolution.Signature.{u}}

/-- Normalized generated Answers of a binary partial algebra. -/
abbrev Generated
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.Free.GeneratedAns D

/-- Finite-tag observational completion of generated Answers. -/
abbrev Completion
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.Filtered.Completion
    (Resolution.External.generatedFilteredSpace D)

/-- Compatible total targets used by the ordinary free-completion universal
    property. The old-carrier map need not be injective. -/
abbrev CompatibleAlg
    (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.Free.CompatibleAlg D

/-- Homomorphisms from generated Answers to compatible total targets. -/
abbrev CompatibleHom
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.CompatibleAlg.{u,v,w} D) :=
  Resolution.Free.CompatibleHom D T

/-- Generated Resolution Answers form the free compatible total extension of
    the original partial algebra. -/
theorem freeCompletionUniversal
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (T : Resolution.Free.CompatibleAlg.{u,v,w} D) :
    ∃ F : Resolution.Free.CompatibleHom D T,
      ∀ G : Resolution.Free.CompatibleHom D T, G = F :=
  Resolution.Free.generatedAns_has_unique_compatibleHom D T

/-- The quotient of the absolutely free expression algebra by equality after
    Resolution embeds injectively into generated Answers. -/
theorem expressionKernelQuotientInjective
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Function.Injective (Resolution.Free.quotientToGenerated D) :=
  Resolution.Free.quotientToGenerated_injective D

/-- Every generated Answer is represented by a class in the expression-kernel
    quotient. -/
theorem expressionKernelQuotientSurjective
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Function.Surjective (Resolution.Free.quotientToGenerated D) :=
  Resolution.Free.quotientToGenerated_surjective D

/-- Distinct generated Answers are separated by an independently specified
    finite-tag preserving total algebra. -/
theorem finiteExternalSeparation
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Resolution.External.FiniteTagSeparating D :=
  Resolution.External.finiteTagSeparating_theorem D

/-- Agreement in every finite-tag observation is exactly generated equality. -/
theorem finiteObservationComplete
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (x y : Generated D) :
    Resolution.External.FiniteTagEq D x y ↔ x = y :=
  Resolution.External.finiteTag_full_abstraction_verified D x y

/-- A pair is separated using at most the sum of its two raw constructor
    counts as fresh finite tags. -/
theorem finiteSeparationBound
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (x y : Generated D) (hxy : x ≠ y) :
    Resolution.External.FiniteTagSeparatesAt D x y
      (Resolution.External.FiniteTagProof.nodeCount D x.1 +
        Resolution.External.FiniteTagProof.nodeCount D y.1) :=
  Resolution.External.finiteTagSeparatesAt_size_bound D x y hxy

/-- Canonical compatible completed total algebra. -/
noncomputable def completedAlgebra
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Resolution.Free.TotalAlg D :=
  Resolution.External.completedResolutionTotalAlg D

/-- The finite-tag completion is complete. -/
theorem completionComplete
    (D : Resolution.PartialAlg.{u,v} Sigma) :
    Resolution.Filtered.Complete
      (Resolution.External.completedResolutionFilteredTotalAlg D).toSpace :=
  Resolution.External.completedResolutionFilteredTotalAlg_complete D

/-- Constant-bearing universal equations hold in the completion exactly when
    they hold in the generated free completion. -/
theorem equationConservative
    {V : Type q}
    (D : Resolution.PartialAlg.{u,v} Sigma)
    (lhs rhs : Resolution.ConstantAlgebraTerm Sigma D.Carrier V) :
    (∀ rho : V -> Completion D,
      Resolution.External.ConstantAlgebraTerm.evalCompleted D rho lhs =
        Resolution.External.ConstantAlgebraTerm.evalCompleted D rho rhs) ↔
    (∀ rho : V -> Generated D,
      Resolution.ConstantAlgebraTerm.evalGenerated D rho lhs =
        Resolution.ConstantAlgebraTerm.evalGenerated D rho rhs) :=
  Resolution.External.completionConstantEquation_iff_generatedConstantEquation
    D lhs rhs

namespace NatDivision

/-- Completed natural-number Resolution carrier. -/
abbrev Completion := Resolution.External.NatArithmetic.Completion

/-- Embed an ordinary natural number. -/
abbrev embed := Resolution.External.NatArithmetic.embedNat

/-- Total completed division. -/
noncomputable def divide (x y : Completion) : Completion :=
  Resolution.External.NatArithmetic.completedDivide x y

/-- Natural division-by-zero Answers retain their numerators. -/
theorem singularFamilyInjective :
    Function.Injective
      (fun a : Nat => divide (embed a) (embed 0)) :=
  Resolution.External.NatArithmetic.completedDivide_zero_injective

/-- Every natural division-by-zero Answer lies outside the old image. -/
theorem singularFamilyDisjoint (a : Nat) :
    ¬ Resolution.External.NatArithmetic.IsOldCompletion
      (divide (embed a) (embed 0)) :=
  Resolution.External.NatArithmetic.completedDivide_zero_not_old a

end NatDivision

namespace IntDivision

/-- Completed integer Resolution carrier. -/
abbrev Completion := Resolution.IntegerArithmetic.Completion

/-- Embed an ordinary integer. -/
abbrev embed := Resolution.IntegerArithmetic.embedInt

/-- Total completed integer division. -/
noncomputable def divide (x y : Completion) : Completion :=
  Resolution.IntegerArithmetic.completedDivide x y

/-- Integer division-by-zero Answers retain their numerators. -/
theorem singularFamilyInjective :
    Function.Injective
      (fun a : Int => divide (embed a) (embed 0)) :=
  Resolution.IntegerArithmetic.completedDivide_zero_injective

/-- Completed integer `0 / 0` is not any embedded old integer. -/
theorem zeroDivZeroNotOld (c : Int) :
    Resolution.IntegerArithmetic.completedZeroDivZero ≠ embed c :=
  Resolution.IntegerArithmetic.completedZeroDivZero_ne_old c

end IntDivision

end ResolutionSemantics
