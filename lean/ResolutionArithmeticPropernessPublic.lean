import ResolutionArithmeticProperness

/-! Public Paper I interface for natural-arithmetic completion properness. -/

namespace ResolutionSemantics
namespace NatDivision

/-- Stage zero does not already separate every pair of generated natural
    arithmetic Answers. -/
theorem stageZeroNotSeparating :
    exists x y : Resolution.Free.GeneratedAns
        Resolution.External.NatArithmetic.alg,
      x ≠ y ∧
        Resolution.External.FiniteTagEqAt
          Resolution.External.NatArithmetic.alg 0 x y :=
  Resolution.ArithmeticProperness.stageZero_not_separating

/-- No finite observation stage is equality on all generated natural
    arithmetic Answers. -/
theorem everyFiniteStageNotEquality (n : Nat) :
    exists x y : Resolution.Free.GeneratedAns
        Resolution.External.NatArithmetic.alg,
      x ≠ y ∧
        Resolution.External.FiniteTagEqAt
          Resolution.External.NatArithmetic.alg n x y :=
  Resolution.ArithmeticProperness.every_stage_not_equality n

/-- The factorial repeated-add-zero sequence is observationally Cauchy. -/
theorem factorialAddZeroCauchy :
    Resolution.Filtered.Cauchy
      (Resolution.External.generatedFilteredSpace
        Resolution.External.NatArithmetic.alg)
      Resolution.ArithmeticProperness.factorialAddZeros :=
  Resolution.ArithmeticProperness.factorialAddZeros_cauchy

/-- The factorial repeated-add-zero sequence has no generated natural-arithmetic
    limit. -/
theorem factorialAddZeroNoLimit
    (x : Resolution.Free.GeneratedAns
      Resolution.External.NatArithmetic.alg) :
    ¬ Resolution.Filtered.Converges
      (Resolution.External.generatedFilteredSpace
        Resolution.External.NatArithmetic.alg)
      Resolution.ArithmeticProperness.factorialAddZeros x :=
  Resolution.ArithmeticProperness.factorialAddZeros_noLimit x

/-- The generated natural-arithmetic filtered space is not complete. -/
theorem notComplete :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace
        Resolution.External.NatArithmetic.alg) :=
  Resolution.ArithmeticProperness.not_complete

/-- The natural-arithmetic completion embedding is not surjective. -/
theorem completionEmbeddingNotSurjective :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace
          Resolution.External.NatArithmetic.alg)) :=
  Resolution.ArithmeticProperness.completionEmbedding_not_surjective

/-- The natural-arithmetic observational completion contains a point outside
    the generated finite-Answer image. -/
theorem completionAddsPoint :
    exists q : Resolution.Filtered.Completion
        (Resolution.External.generatedFilteredSpace
          Resolution.External.NatArithmetic.alg),
      forall x : Resolution.Free.GeneratedAns
          Resolution.External.NatArithmetic.alg,
        Resolution.Filtered.embed
            (Resolution.External.generatedFilteredSpace
              Resolution.External.NatArithmetic.alg) x ≠ q :=
  Resolution.ArithmeticProperness.completion_adds_point

end NatDivision
end ResolutionSemantics
