import ResolutionOldFixingContextProperness
import ResolutionSemantics

/-! Public Paper I interface for the old-fixing-context properness criterion. -/

universe u v

namespace ResolutionSemantics
namespace OldFixingContextCompletion

variable {Sigma : Resolution.Signature.{u}}

/-- An undefined old seed together with a context `x ↦ u(x,e)` that fixes
    every old element. -/
abbrev Witness (D : Resolution.PartialAlg.{u,v} Sigma) :=
  Resolution.OldFixingContextWitness D

/-- The factorially sampled orbit associated with a witness. -/
abbrev factorialSequence
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) :=
  Resolution.OldFixingContextProperness.factorialIterates D W

/-- The witness produces a Cauchy sequence without requiring a finite old
    carrier. -/
theorem factorialSequenceCauchy
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) :
    Resolution.Filtered.Cauchy
      (Resolution.External.generatedFilteredSpace D)
      (factorialSequence D W) :=
  Resolution.OldFixingContextProperness.factorialIterates_cauchy D W

/-- The witness sequence has no generated limit. -/
theorem factorialSequenceNoLimit
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D)
    (x : Resolution.Free.GeneratedAns D) :
    ¬ Resolution.Filtered.Converges
      (Resolution.External.generatedFilteredSpace D)
      (factorialSequence D W) x :=
  Resolution.OldFixingContextProperness.factorialIterates_noLimit D W x

/-- Every finite observation stage is strictly coarser than equality. -/
theorem everyFiniteStageNotEquality
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) (n : Nat) :
    exists x y : Resolution.Free.GeneratedAns D,
      x ≠ y ∧ Resolution.External.FiniteTagEqAt D n x y :=
  Resolution.OldFixingContextProperness.every_stage_not_equality D W n

/-- The explicit stage-`n` witness pair has separation rank greater than `n`;
    in particular, the finite-complement separation ranks are unbounded. -/
theorem separationRankGreaterThanBudget
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) (n : Nat) :
    n < Resolution.External.finiteSeparationRank D
      (factorialSequence D W (n + 2))
      (factorialSequence D W (n + 3)) :=
  Resolution.OldFixingContextProperness.factorialPair_separationRank_gt D W n

/-- The generated observational space is not complete. -/
theorem notComplete
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace D) :=
  Resolution.OldFixingContextProperness.not_complete D W

/-- An old-fixing context witness forces the completion embedding to be
    non-surjective, independently of the cardinality of the old carrier. -/
theorem embeddingNotSurjective
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace D)) :=
  Resolution.OldFixingContextProperness.completionEmbedding_not_surjective D W

/-- The completion contains an explicit point outside the generated image. -/
theorem addsPoint
    (D : Resolution.PartialAlg.{u,v} Sigma) (W : Witness D) :
    exists q : Resolution.Filtered.Completion
        (Resolution.External.generatedFilteredSpace D),
      forall x : Resolution.Free.GeneratedAns D,
        Resolution.Filtered.embed
            (Resolution.External.generatedFilteredSpace D) x ≠ q :=
  Resolution.OldFixingContextProperness.completion_adds_point D W

end OldFixingContextCompletion

namespace NatDivision

/-- Natural arithmetic has the old-fixing context `x ↦ x + 0`, based at the
    undefined seed `0 / 0`. -/
def oldFixingContextWitness :
    Resolution.OldFixingContextWitness
      Resolution.External.NatArithmetic.alg where
  seedOp := Resolution.External.NatArithmetic.Op.div
  seedLeft := 0
  seedRight := 0
  seedUndefined := Resolution.External.NatArithmetic.eval_div_zero 0
  stepOp := Resolution.External.NatArithmetic.Op.add
  fixedRight := 0
  fixesOld := by
    intro a
    simpa using Resolution.External.NatArithmetic.eval_add a 0

/-- The generic criterion independently recovers natural-arithmetic
    properness. -/
theorem oldFixingCriterion :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace
          Resolution.External.NatArithmetic.alg)) :=
  OldFixingContextCompletion.embeddingNotSurjective
    Resolution.External.NatArithmetic.alg oldFixingContextWitness

/-- Natural-arithmetic finite separation ranks are unbounded along the
    repeated-`+ 0` factorial family. -/
theorem separationRanksUnbounded (n : Nat) :
    n < Resolution.External.finiteSeparationRank
      Resolution.External.NatArithmetic.alg
      (OldFixingContextCompletion.factorialSequence
        Resolution.External.NatArithmetic.alg oldFixingContextWitness (n + 2))
      (OldFixingContextCompletion.factorialSequence
        Resolution.External.NatArithmetic.alg oldFixingContextWitness (n + 3)) :=
  OldFixingContextCompletion.separationRankGreaterThanBudget
    Resolution.External.NatArithmetic.alg oldFixingContextWitness n

end NatDivision

namespace IntDivision

/-- Integer arithmetic has the same old-fixing context `x ↦ x + 0`, based at
    the undefined seed `0 / 0`. -/
def oldFixingContextWitness :
    Resolution.OldFixingContextWitness Resolution.IntegerArithmetic.alg where
  seedOp := Resolution.IntegerArithmetic.Op.div
  seedLeft := 0
  seedRight := 0
  seedUndefined := Resolution.IntegerArithmetic.partialEval_div_zero 0
  stepOp := Resolution.IntegerArithmetic.Op.add
  fixedRight := 0
  fixesOld := by
    intro a
    simpa using Resolution.IntegerArithmetic.partialEval_add a 0

/-- Every finite integer-arithmetic observation stage is strictly coarser
    than equality. -/
theorem everyFiniteStageNotEquality (n : Nat) :
    exists x y : Resolution.Free.GeneratedAns Resolution.IntegerArithmetic.alg,
      x ≠ y ∧ Resolution.External.FiniteTagEqAt
        Resolution.IntegerArithmetic.alg n x y :=
  OldFixingContextCompletion.everyFiniteStageNotEquality
    Resolution.IntegerArithmetic.alg oldFixingContextWitness n

/-- The old-fixing factorial sequence for integer arithmetic is Cauchy. -/
theorem factorialOldFixingCauchy :
    Resolution.Filtered.Cauchy
      (Resolution.External.generatedFilteredSpace
        Resolution.IntegerArithmetic.alg)
      (OldFixingContextCompletion.factorialSequence
        Resolution.IntegerArithmetic.alg oldFixingContextWitness) :=
  OldFixingContextCompletion.factorialSequenceCauchy
    Resolution.IntegerArithmetic.alg oldFixingContextWitness

/-- The integer old-fixing factorial sequence has no generated limit. -/
theorem factorialOldFixingNoLimit
    (x : Resolution.Free.GeneratedAns Resolution.IntegerArithmetic.alg) :
    ¬ Resolution.Filtered.Converges
      (Resolution.External.generatedFilteredSpace
        Resolution.IntegerArithmetic.alg)
      (OldFixingContextCompletion.factorialSequence
        Resolution.IntegerArithmetic.alg oldFixingContextWitness) x :=
  OldFixingContextCompletion.factorialSequenceNoLimit
    Resolution.IntegerArithmetic.alg oldFixingContextWitness x

/-- Integer arithmetic is not complete for finite-tag observation. -/
theorem notComplete :
    ¬ Resolution.Filtered.Complete
      (Resolution.External.generatedFilteredSpace
        Resolution.IntegerArithmetic.alg) :=
  OldFixingContextCompletion.notComplete
    Resolution.IntegerArithmetic.alg oldFixingContextWitness

/-- The integer-arithmetic completion embedding is not surjective. -/
theorem completionEmbeddingNotSurjective :
    ¬ Function.Surjective
      (Resolution.Filtered.embed
        (Resolution.External.generatedFilteredSpace
          Resolution.IntegerArithmetic.alg)) :=
  OldFixingContextCompletion.embeddingNotSurjective
    Resolution.IntegerArithmetic.alg oldFixingContextWitness

/-- The integer-arithmetic completion contains a point outside the generated
    finite-Answer image. -/
theorem completionAddsPoint :
    exists q : Resolution.Filtered.Completion
        (Resolution.External.generatedFilteredSpace
          Resolution.IntegerArithmetic.alg),
      forall x : Resolution.Free.GeneratedAns Resolution.IntegerArithmetic.alg,
        Resolution.Filtered.embed
            (Resolution.External.generatedFilteredSpace
              Resolution.IntegerArithmetic.alg) x ≠ q :=
  OldFixingContextCompletion.addsPoint
    Resolution.IntegerArithmetic.alg oldFixingContextWitness

/-- Integer-arithmetic finite separation ranks are unbounded along the
    old-fixing factorial family. -/
theorem separationRanksUnbounded (n : Nat) :
    n < Resolution.External.finiteSeparationRank
      Resolution.IntegerArithmetic.alg
      (OldFixingContextCompletion.factorialSequence
        Resolution.IntegerArithmetic.alg oldFixingContextWitness (n + 2))
      (OldFixingContextCompletion.factorialSequence
        Resolution.IntegerArithmetic.alg oldFixingContextWitness (n + 3)) :=
  OldFixingContextCompletion.separationRankGreaterThanBudget
    Resolution.IntegerArithmetic.alg oldFixingContextWitness n

end IntDivision
end ResolutionSemantics
