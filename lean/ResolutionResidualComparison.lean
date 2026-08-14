import ResolutionIntrinsicFiniteComplement
import ResolutionFiniteBaseProperness
import ResolutionFreeCompletionFinal

/-!
# Residual-finiteness and Rees-index comparison

This module records two precise comparisons for the paper.

* When the old carrier has a finite code, intrinsic finite-complement
  separation supplies an ordinary finite compatible target for every distinct
  pair of generated Answers.  The construction retains the explicit state
  bound coming from the finite-tag separator.
* The embedded old carrier is closed under the total operations of the
  generated Answer algebra exactly when the original partial evaluator was
  already total.  Thus, in the genuinely partial case, the old carrier is not
  a total subalgebra of the generated completion, which is the structural
  reason that ordinary finite Rees index is only an analogy.
-/

universe u v w

namespace Resolution
namespace ResidualComparison

open Resolution.External
open Resolution.External.FiniteTagProof
open Resolution.Orbit

variable {Sigma : Signature.{u}}

/-! ## Finite compatible targets -/

/-- Forget the injectivity requirement on the old-carrier map of a compatible
    total extension. -/
def totalAlgToCompatibleAlg
    {D : PartialAlg.{u,v} Sigma}
    (T : Free.TotalAlg.{u,v,w} D) :
    Free.CompatibleAlg.{u,v,w} D where
  Carrier := T.Carrier
  embed := T.embed
  op := T.op
  preserve := T.preserve

theorem foldRaw_totalAlgToCompatibleAlg
    {D : PartialAlg.{u,v} Sigma}
    (T : Free.TotalAlg.{u,v,w} D) :
    forall r : RawAns Sigma D.Carrier,
      Free.CompatibleAlg.foldRaw D (totalAlgToCompatibleAlg T) r =
        Free.TotalAlg.foldRaw D T r
  | .old _ => rfl
  | .susp _ x y => by
      simp only [Free.CompatibleAlg.foldRaw, Free.TotalAlg.foldRaw]
      rw [foldRaw_totalAlgToCompatibleAlg T x,
        foldRaw_totalAlgToCompatibleAlg T y]
      rfl

theorem interp_totalAlgToCompatibleAlg
    {D : PartialAlg.{u,v} Sigma}
    (T : Free.TotalAlg.{u,v,w} D)
    (x : Free.GeneratedAns D) :
    Free.CompatibleAlg.interp D (totalAlgToCompatibleAlg T) x =
      Free.TotalAlg.interp D T x :=
  foldRaw_totalAlgToCompatibleAlg T x.1

/-- A pair of generated Answers is separated by a compatible target whose
    whole carrier has an explicit finite code.  The old-carrier map is not
    required to be injective in this definition, matching ordinary
    homomorphic residual separation. -/
def FiniteCompatibleSeparatesAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : Prop :=
  Exists fun targetSize : Nat =>
    Exists fun T : Free.CompatibleAlg.{u,v,v} D =>
      Exists fun _ : Coded T.Carrier targetSize =>
        Free.CompatibleAlg.interp D T x ≠
          Free.CompatibleAlg.interp D T y

/-- Ordinary residual finiteness of the generated Answer algebra, expressed
    using finite compatible targets for the old generators. -/
def GeneratedResiduallyFinite
    (D : PartialAlg.{u,v} Sigma) : Prop :=
  forall {x y : Free.GeneratedAns D}, x ≠ y ->
    FiniteCompatibleSeparatesAt D x y

/-- Over a base coded by `baseSize`, a distinct pair has a compatible
    separating target with at most the base size, the two constructor counts,
    and one reserve state. -/
theorem finiteBaseCompatibleSeparationBound
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize)
    (x y : Free.GeneratedAns D) (hxy : x ≠ y) :
    Exists fun T : Free.CompatibleAlg.{u,v,v} D =>
      Exists fun _ : Coded T.Carrier
          (baseSize + nodeCount D x.1 + nodeCount D y.1 + 1) =>
        Function.Injective T.embed ∧
          Free.CompatibleAlg.interp D T x ≠
            Free.CompatibleAlg.interp D T y := by
  let n := nodeCount D x.1 + nodeCount D y.1
  rcases finiteTagSeparatesAt_size_bound D x y hxy with ⟨T, hT⟩
  let target := totalAlgToCompatibleAlg (T.toTotalAlg D)
  refine ⟨target, ?_, ?_, ?_⟩
  · change Coded (FiniteTagCarrier D n)
      (baseSize + nodeCount D x.1 + nodeCount D y.1 + 1)
    have code := FiniteBaseProperness.finiteTagCoded D C n
    simpa [n, Nat.add_assoc] using code
  · exact (T.toTotalAlg D).embed_injective
  · change Free.CompatibleAlg.interp D target x ≠
      Free.CompatibleAlg.interp D target y
    rw [interp_totalAlgToCompatibleAlg, interp_totalAlgToCompatibleAlg]
    exact hT

/-- Every generated Answer algebra over a finitely coded base is residually
    finite in the ordinary homomorphic sense. -/
theorem finiteBaseGeneratedResiduallyFinite
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize) :
    GeneratedResiduallyFinite D := by
  intro x y hxy
  let targetSize :=
    baseSize + nodeCount D x.1 + nodeCount D y.1 + 1
  rcases finiteBaseCompatibleSeparationBound D C x y hxy with
    ⟨T, hCode, _, hSep⟩
  exact ⟨targetSize, T, hCode, hSep⟩

/-! ## Closure of the old image -/

/-- The old image is closed under the generated total operations.  This is
    exactly the condition needed for it to be a total subalgebra, as opposed
    to merely the pointwise-preserved partial base. -/
def GeneratedOldClosed
    (D : PartialAlg.{u,v} Sigma) : Prop :=
  forall (f : Sigma.Op) (a b : D.Carrier),
    Exists fun c : D.Carrier =>
      Free.generatedOp D f (Free.generatedOld D a)
          (Free.generatedOld D b) =
        Free.generatedOld D c

/-- An undefined old application leaves the embedded old image in the
    generated Answer algebra. -/
theorem undefinedApplicationEscapesOldImage
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a b : D.Carrier)
    (hUndefined : D.eval f a b = none) :
    forall c : D.Carrier,
      Free.generatedOp D f (Free.generatedOld D a)
          (Free.generatedOld D b) ≠
        Free.generatedOld D c := by
  intro c hEq
  have hVal := congrArg Subtype.val hEq
  simp only [Free.generatedOp_val, Free.generatedOld_val] at hVal
  simp [PartialAlg.liftOp, hUndefined] at hVal

/-- The old image is a total subalgebra of the generated Answer algebra if
    and only if the original partial evaluator was already total. -/
theorem generatedOldClosed_iff_evaluatorTotal
    (D : PartialAlg.{u,v} Sigma) :
    GeneratedOldClosed D ↔ FiniteBaseProperness.IsTotal D := by
  constructor
  · intro hClosed f a b
    rcases hClosed f a b with ⟨c, hOld⟩
    cases hEval : D.eval f a b with
    | none =>
        exact False.elim
          (undefinedApplicationEscapesOldImage D f a b hEval c hOld)
    | some d =>
        exact ⟨d, rfl⟩
  · intro hTotal f a b
    rcases hTotal f a b with ⟨c, hEval⟩
    exact ⟨c, Free.generatedOp_old_of_defined D f a b c hEval⟩

end ResidualComparison
end Resolution
