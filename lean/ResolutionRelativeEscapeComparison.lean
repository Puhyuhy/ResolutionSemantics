import ResolutionFinitePatternAntiLimit
import ResolutionPropernessCriteriaComparison

/-!
# Relative finite-pattern escape beyond ordinary finite targets

The no-limit conclusion of finite-pattern escape has close analogues in
ordinary profinite settings: a candidate can be isolated by a finite recognizer
while a Cauchy sequence converges to a new profinite point.  The structurally
distinct feature of Resolution Semantics over an infinite base is therefore not
candidate-tailored separation in the abstract.

This module isolates the stronger relative fact.  The concrete escape observer
fixes the entire base pointwise and uses only finitely many extra tags plus
one overflow state.  If the base itself admits no finite injective code, then
no finitely coded target can contain it injectively at all; in particular the
escape observer carrier is necessarily non-finite as a whole.  Nevertheless
the same observer separates the chosen generated candidate from the entire
sufficiently late syntactic tail.

Thus, under a non-finitely-codable base, the Resolution escape witness cannot
be replaced by an ordinary finite target without abandoning injective
pointwise base preservation.
-/

universe u v w

namespace Resolution
namespace RelativeEscapeComparison

open Resolution.External
open Resolution.Orbit
open Resolution.External.FiniteTagProof
open Resolution.External.FinitePatternRealization
open Resolution.OrbitCompression
open Resolution.FinitePatternAntiLimit

variable {Sigma : Signature.{u}}

/-- A non-finitely-codable base cannot embed injectively into any finitely
coded target.  This is the direct obstruction to replacing a relative observer
by an ordinary finite target while retaining every base point distinctly. -/
theorem no_finitely_coded_target_with_injective_base
    {A : Type v} {T : Type w}
    (hBase : forall m : Nat, Not (Nonempty (Coded A m)))
    (embed : A -> T)
    (hInjective : Function.Injective embed)
    (m : Nat) :
    Not (Nonempty (Coded T m)) := by
  rintro ⟨C⟩
  let B : Coded A m := {
    code := fun a => C.code (embed a)
    code_lt := fun a => C.code_lt (embed a)
    code_inj := by
      intro a b h
      apply hInjective
      exact C.code_inj _ _ h
  }
  exact hBase m ⟨B⟩

/-- If the distinguished base has no injective code into any finite type, then
neither does any canonical finite-tag carrier over that base.  The extra part
is finite, but the pointwise-preserved base remains fully present. -/
theorem finiteTagCarrier_not_finitely_codable_of_base
    (D : PartialAlg.{u,v} Sigma)
    (hBase : forall m : Nat, Not (Nonempty (Coded D.Carrier m)))
    (n m : Nat) :
    Not (Nonempty (Coded (FiniteTagCarrier D n) m)) := by
  exact no_finitely_coded_target_with_injective_base
    hBase
    (fun a : D.Carrier => (Sum.inl a : FiniteTagCarrier D n))
    (by
      intro a b h
      exact Sum.inl.inj h)
    m

/-- The candidate-tailored pattern observer does more than witness
non-convergence abstractly: once the first unseen continuation falls into
`overflow`, the same observer separates the chosen candidate from every later
term in the unary syntactic tail. -/
theorem escapeObserver_eventuallySeparatesCandidate
    (D : PartialAlg.{u,v} Sigma)
    (W : ObserverOrbitCompression D)
    (U : EscapingUnarySyntax W)
    (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    forall d : Nat,
      Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) x.1 ≠
        Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D)
          (W.term (nodeCount D x.1 + 2 + d)).1 := by
  dsimp only
  intro d hEq
  have hx := fold_candidate_eq_encode D W x
  have ht := fold_escapeTail_eq_overflow D W U x d
  rw [hx, ht] at hEq
  have hmem := candidate_mem_escapeSelected D W x
  exact patternEncode_ne_overflow_of_mem D hmem hEq

/-- Structural separation from ordinary finite-target profinite recognition.
If the pointwise-preserved base is not finitely codable, then the actual
candidate-tailored escape observer is necessarily non-finite as a whole,
although its external complement is finite.  The same non-finite relative
observer still separates the candidate from the whole late tail. -/
theorem relativeEscapeBeyondOrdinaryFiniteTargets
    (D : PartialAlg.{u,v} Sigma)
    (hBase : forall m : Nat, Not (Nonempty (Coded D.Carrier m)))
    (W : ObserverOrbitCompression D)
    (U : EscapingUnarySyntax W)
    (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    (forall d : Nat,
      Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) x.1 ≠
        Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D)
          (W.term (nodeCount D x.1 + 2 + d)).1) ∧
    (forall m : Nat,
      Not (Nonempty
        (Coded
          (FiniteTagCarrier D (patternSelected D roots).length) m))) := by
  dsimp only
  constructor
  · exact escapeObserver_eventuallySeparatesCandidate D W U x
  · intro m
    exact finiteTagCarrier_not_finitely_codable_of_base D hBase _ m

/-- Natural-number bases satisfy the non-finite-codability hypothesis used by
the structural comparison theorem. -/
theorem natBase_not_finitely_codable
    (m : Nat) :
    Not (Nonempty (Coded Nat m)) :=
  ResolutionSemantics.PropernessCriteria.natHasNoFiniteCode m

/-- In the natural-arithmetic instance, every candidate-tailored escape
observer supplied by the generic construction separates the late tail while
being impossible to encode into any ordinary finite carrier. -/
theorem natRelativeEscapeBeyondOrdinaryFiniteTargets
    (W : ObserverOrbitCompression Resolution.External.NatArithmetic.alg)
    (U : EscapingUnarySyntax W)
    (x : Free.GeneratedAns Resolution.External.NatArithmetic.alg) :
    let roots := escapeRoots W x
    (forall d : Nat,
      Free.TotalAlg.foldRaw Resolution.External.NatArithmetic.alg
          ((patternAlg Resolution.External.NatArithmetic.alg roots).toTotalAlg
            Resolution.External.NatArithmetic.alg) x.1 ≠
        Free.TotalAlg.foldRaw Resolution.External.NatArithmetic.alg
          ((patternAlg Resolution.External.NatArithmetic.alg roots).toTotalAlg
            Resolution.External.NatArithmetic.alg)
          (W.term
            (nodeCount Resolution.External.NatArithmetic.alg x.1 + 2 + d)).1) ∧
    (forall m : Nat,
      Not (Nonempty
        (Coded
          (FiniteTagCarrier Resolution.External.NatArithmetic.alg
            (patternSelected Resolution.External.NatArithmetic.alg roots).length)
          m))) :=
  relativeEscapeBeyondOrdinaryFiniteTargets
    Resolution.External.NatArithmetic.alg natBase_not_finitely_codable W U x

end RelativeEscapeComparison
end Resolution
