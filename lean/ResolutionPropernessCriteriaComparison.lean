import ResolutionFiniteBasePropernessPublic
import ResolutionOldFixingContextPropernessPublic
import ResolutionSemanticsCompletion

/-!
# Comparison of the two properness criteria

The finite-base and old-fixing-context hypotheses are incomparable.  The
one-point always-undefined algebra satisfies the finite-base hypothesis but has
no old-fixing context.  Natural arithmetic has an old-fixing context but no
finite code for its old carrier.
-/

namespace ResolutionSemantics
namespace PropernessCriteria

/-- The one-point carrier has an explicit one-state code. -/
def onePointCode :
    Resolution.Orbit.Coded Resolution.OnePoint.alg.Carrier 1 where
  code := fun _ => 0
  code_lt := by
    intro _
    omega
  code_inj := by
    intro a b _
    cases a
    cases b
    rfl

/-- The one-point example is covered by the finite-base criterion and has a
    proper completion, but it has no old-fixing-context witness. -/
theorem onePointProperWithoutOldFixing :
    Nonempty
        (Resolution.Orbit.Coded Resolution.OnePoint.alg.Carrier 1) ∧
      (∃ f : Resolution.OnePoint.signature.Op,
        ∃ a b : Resolution.OnePoint.alg.Carrier,
          Resolution.OnePoint.alg.eval f a b = none) ∧
      (¬ Function.Surjective
        (Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace
            Resolution.OnePoint.alg))) ∧
      ¬ Nonempty
        (Resolution.OldFixingContextWitness Resolution.OnePoint.alg) := by
  refine ⟨⟨onePointCode⟩, ⟨(), (), (), rfl⟩,
    ResolutionSemantics.OnePointCompletion.embeddingNotSurjective, ?_⟩
  rintro ⟨W⟩
  have hfix := W.fixesOld ()
  simp [Resolution.OnePoint.alg] at hfix

/-- No finite bound can code the natural numbers injectively. -/
theorem natHasNoFiniteCode (m : Nat) :
    ¬ Nonempty (Resolution.Orbit.Coded Nat m) := by
  rintro ⟨C⟩
  have hb : ∀ i : Nat, i ≤ m → C.code i < m := by
    intro i _
    exact C.code_lt i
  rcases Resolution.Pigeon.boundedRepeat m C.code hb with
    ⟨i, j, hij, _hj, heq⟩
  have hsame : i = j := C.code_inj i j heq
  omega

/-- Natural arithmetic is covered by the old-fixing-context criterion and has
    a proper completion, but its old carrier has no finite code. -/
theorem natProperWithoutFiniteCoding :
    Nonempty
        (Resolution.OldFixingContextWitness
          Resolution.External.NatArithmetic.alg) ∧
      (¬ Function.Surjective
        (Resolution.Filtered.embed
          (Resolution.External.generatedFilteredSpace
            Resolution.External.NatArithmetic.alg))) ∧
      ∀ m : Nat,
        ¬ Nonempty
          (Resolution.Orbit.Coded
            Resolution.External.NatArithmetic.alg.Carrier m) := by
  exact ⟨⟨ResolutionSemantics.NatDivision.oldFixingContextWitness⟩,
    ResolutionSemantics.NatDivision.oldFixingCriterion,
    natHasNoFiniteCode⟩

end PropernessCriteria
end ResolutionSemantics
