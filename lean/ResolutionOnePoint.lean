import ResolutionCompletionProbe
import ResolutionOrbit

/-!
# The one-point algebra: its combs at factorial indices are Cauchy

This is the bridge between the orbit machinery of `ResolutionOrbit.lean` and the
Resolution definitions, for the witness of `paper/COMPLETION-ADDS-POINTS.md`.

Let `D₁` be the **one-point partial algebra**: `Carrier = Unit`, one binary
operation symbol, and every application undefined. Because `preserve` is vacuous
there, a stage-`n` observer is completely unconstrained, and because a comb's
right operand is always the old point, the observer's entire effect on the comb
family is a single function

```
obsStep T : TagState n -> TagState n,   obsStep T s = T.op () s (old ())
```

iterated from the state of `old ()`. That is `foldComb_eq_orb`, and it turns a
statement quantified over all models into a statement about orbits, where
`Resolution.Orbit.orbit_eq_of_factorial_dvd` applies.

The consequence proved here is `factorialCombs_cauchy`: the combs at factorial
indices form a Cauchy sequence in the finite-tag observational filtration. A
stage-`n` observer has only `n + 2` states, so its orbit is eventually periodic
with period dividing `(n+2)!`, and every sufficiently late factorial index is a
multiple of `(n+2)!`.

What is **not** proved here is that this sequence has no limit; that is the
remaining half of the witness and it is stated as `NoLimitStatement` below
without proof, so nothing in this file asserts it.
-/

namespace Resolution
namespace OnePoint

open Resolution.External
open Resolution.Orbit

/-! ## The algebra -/

/-- One binary operation symbol. -/
abbrev signature : Signature := { Op := Unit }

/-- The one-point partial algebra: a single old value, and every application
    undefined. `abbrev` keeps the carrier transparently `Unit`, so the finite-tag
    carrier is definitionally `TagState n`. -/
abbrev alg : PartialAlg signature where
  Carrier := Unit
  eval := fun _ _ _ => none

theorem eval_none (f : signature.Op) (a b : alg.Carrier) :
    alg.eval f a b = none := rfl

/-- The `k`-th comb: `k` iterated applications of the undefined operation. -/
noncomputable def comb (k : Nat) : Free.GeneratedAns alg :=
  Probe.comb alg () () () k

/-! ## A stage-`n` observer acts on combs as a single map -/

variable {n : Nat}

/-- The old point's state in a stage-`n` model. -/
def basePoint : TagState n := Sum.inl ()

/-- The observer's whole effect on the comb family: apply the operation with the
    old point on the right. -/
def obsStep (T : FiniteTagAlg alg n) : TagState n -> TagState n :=
  fun s => T.op () s (Sum.inl ())

/-- **The bridge.** Folding the `k`-th comb is iterating `obsStep` `k` times. -/
theorem foldComb_eq_orb (T : FiniteTagAlg alg n) :
    forall k : Nat,
      Free.TotalAlg.foldRaw alg (T.toTotalAlg alg)
          (Probe.combRaw alg () () () k) =
        orb (obsStep T) basePoint k
  | 0 => rfl
  | k + 1 => by
      rw [Probe.combRaw_succ alg () () () (eval_none () () ()) k]
      show T.op ()
          (Free.TotalAlg.foldRaw alg (T.toTotalAlg alg)
            (Probe.combRaw alg () () () k))
          (Sum.inl ()) = _
      rw [foldComb_eq_orb T k]
      rfl

/-- Past index `n + 2`, comb indices congruent modulo `(n+2)!` are
    observationally indistinguishable at stage `n`. -/
theorem comb_eqAt_of_factorial_dvd
    {i j : Nat} (hi : n + 2 <= i) (hij : i <= j)
    (hdvd : fact (n + 2) ∣ (j - i)) :
    FiniteTagEqAt alg n (comb i) (comb j) := by
  intro T
  show Free.TotalAlg.foldRaw alg (T.toTotalAlg alg)
      (Probe.combRaw alg () () () i) =
    Free.TotalAlg.foldRaw alg (T.toTotalAlg alg)
      (Probe.combRaw alg () () () j)
  rw [foldComb_eq_orb T i, foldComb_eq_orb T j]
  exact orbit_eq_of_factorial_dvd (obsStep T) basePoint (tagCoded n) hi hij hdvd

/-! ## The Cauchy sequence -/

/-- The combs at factorial indices. -/
noncomputable def factorialCombs (k : Nat) : Free.GeneratedAns alg :=
  comb (fact k)

/-- A shared divisor of two numbers divides their difference. `Std` has no
    `Nat.dvd_sub'`, so it is proved here. -/
theorem dvd_sub_of_dvd_of_dvd {a b c : Nat}
    (hb : a ∣ b) (hc : a ∣ c) : a ∣ (c - b) := by
  rcases hb with ⟨x, hx⟩
  rcases hc with ⟨y, hy⟩
  exact ⟨y - x, by rw [hx, hy, Nat.mul_sub_left_distrib]⟩

/-- Any two sufficiently late factorial indices are indistinguishable at
    stage `n`. -/
theorem factorialCombs_eqAt
    {i j : Nat} (hi : n + 2 <= i) (hj : n + 2 <= j) :
    FiniteTagEqAt alg n (factorialCombs i) (factorialCombs j) := by
  have hdvd_i : fact (n + 2) ∣ fact i := fact_dvd_fact _ _ hi
  have hdvd_j : fact (n + 2) ∣ fact j := fact_dvd_fact _ _ hj
  have hbi : n + 2 <= fact i := Nat.le_trans hi (le_fact i)
  have hbj : n + 2 <= fact j := Nat.le_trans hj (le_fact j)
  rcases Nat.le_total (fact i) (fact j) with hle | hle
  · exact comb_eqAt_of_factorial_dvd hbi hle
      (dvd_sub_of_dvd_of_dvd hdvd_i hdvd_j)
  · exact finiteTagEqAt_symm alg n
      (comb_eqAt_of_factorial_dvd hbj hle
        (dvd_sub_of_dvd_of_dvd hdvd_j hdvd_i))

/-- **The combs at factorial indices are Cauchy.** This is the half of the
    completion witness that needed the counting argument: a stage-`n` observer
    has `n + 2` states, so its orbit is eventually periodic with period dividing
    `(n+2)!`, and every factorial index past `n + 2` is a multiple of it. -/
theorem factorialCombs_cauchy :
    Filtered.Cauchy (generatedFilteredSpace alg) factorialCombs := by
  intro m
  exact ⟨m + 2, fun i j hi hj => factorialCombs_eqAt hi hj⟩

/-! ## The sequence has no limit

A limit may be *any* generated Answer, and for this algebra those are all binary
trees over the one old point, not only combs. Rather than analyse tree shape, we
use an observer that simply **counts nodes up to a cap**: it sends a state pair
to the state whose value is the sum of their values plus two, saturating at the
top state. Folding then computes `min (nodeCount t) (n + 2)` uniformly, with no
case analysis on the shape of `t`.

Since a comb's node count grows without bound while any fixed Answer's does not,
a large enough state budget separates that Answer from all sufficiently late
combs. -/

/-- Decode a value into a state, saturating at the top. -/
def ofVal (n : Nat) (v : Nat) : Orbit.TagState n :=
  if h0 : v = 0 then Sum.inl ()
  else if h : v <= n then Sum.inr (Sum.inl ⟨v - 1, by omega⟩)
  else Sum.inr (Sum.inr ())

@[simp] theorem tagCode_ofVal (n v : Nat) :
    Orbit.tagCode (ofVal n v) = min v (n + 1) := by
  unfold ofVal
  split
  · next h0 => subst h0; show (0 : Nat) = _; omega
  · next h0 =>
      split
      · next h => show (v - 1) + 1 = _; omega
      · next h => show n + 1 = _; omega

/-- The node-counting observer: values add, saturating at the top state. -/
def countOp (n : Nat) :
    signature.Op -> Orbit.TagState n -> Orbit.TagState n -> Orbit.TagState n :=
  fun _ s t => ofVal n (Orbit.tagCode s + Orbit.tagCode t + 2)

/-- `preserve` is vacuous for this algebra, so any table is a legal model. -/
def countModel (n : Nat) : FiniteTagAlg alg n where
  op := countOp n
  preserve := by
    intro f a b c h
    have h' : (none : Option alg.Carrier) = some c := h
    simp at h'

theorem nodeCount_pos :
    forall t : RawAns signature alg.Carrier,
      0 < FiniteTagProof.nodeCount alg t
  | .old _ => Nat.zero_lt_one
  | .susp _ l r => by
      show 0 < 1 + (FiniteTagProof.nodeCount alg l
        + FiniteTagProof.nodeCount alg r)
      omega

/-- **The counting observer computes capped node count**, uniformly in the shape
    of the Answer. -/
theorem foldVal (n : Nat) :
    forall t : RawAns signature alg.Carrier,
      Orbit.tagCode
          (Free.TotalAlg.foldRaw alg ((countModel n).toTotalAlg alg) t) + 1
        = min (FiniteTagProof.nodeCount alg t) (n + 2)
  | .old _ => by show (0 : Nat) + 1 = min 1 (n + 2); omega
  | .susp f l r => by
      have ihl := foldVal n l
      have ihr := foldVal n r
      have hpl := nodeCount_pos l
      have hpr := nodeCount_pos r
      have hstep :
          Free.TotalAlg.foldRaw alg ((countModel n).toTotalAlg alg)
              (.susp f l r)
            = ofVal n
              (Orbit.tagCode (Free.TotalAlg.foldRaw alg
                  ((countModel n).toTotalAlg alg) l)
                + Orbit.tagCode (Free.TotalAlg.foldRaw alg
                  ((countModel n).toTotalAlg alg) r) + 2) := rfl
      rw [hstep, tagCode_ofVal]
      show _ = min (1 + (FiniteTagProof.nodeCount alg l
        + FiniteTagProof.nodeCount alg r)) (n + 2)
      omega

/-- The factorial combs have no limit: any candidate Answer is separated from
    all sufficiently late combs by the counting observer at a stage exceeding
    the candidate's size. -/
theorem noLimit :
    forall x : Free.GeneratedAns alg,
      ¬ Filtered.Converges (generatedFilteredSpace alg) factorialCombs x := by
  intro x hconv
  rcases hconv (FiniteTagProof.nodeCount alg x.1) with ⟨N, hN⟩
  -- an index that is both late enough for `hN` and large enough to saturate
  have hk := hN (N + FiniteTagProof.nodeCount alg x.1 + 2) (by omega)
  have hfold := hk (countModel (FiniteTagProof.nodeCount alg x.1))
  -- read both sides through the counting observer
  have hx := foldVal (FiniteTagProof.nodeCount alg x.1) x.1
  have hc := foldVal (FiniteTagProof.nodeCount alg x.1)
    (Probe.combRaw alg () () ()
      (fact (N + FiniteTagProof.nodeCount alg x.1 + 2)))
  rw [Probe.combRaw_nodeCount alg () () () (eval_none () () ()) _] at hc
  have hgrow : N + FiniteTagProof.nodeCount alg x.1 + 2
      <= fact (N + FiniteTagProof.nodeCount alg x.1 + 2) :=
    le_fact _
  -- `interp` is `foldRaw` on the underlying raw Answer, definitionally
  have hfold2 :
      Free.TotalAlg.foldRaw alg
          ((countModel (FiniteTagProof.nodeCount alg x.1)).toTotalAlg alg) x.1
        = Free.TotalAlg.foldRaw alg
          ((countModel (FiniteTagProof.nodeCount alg x.1)).toTotalAlg alg)
          (Probe.combRaw alg () () ()
            (fact (N + FiniteTagProof.nodeCount alg x.1 + 2))) := hfold
  have hcong := congrArg Orbit.tagCode hfold2
  omega

/-- **The one-point algebra's observational filtration is not complete.** Its
    completion therefore strictly contains the generated algebra: the completion
    is not vacuous. -/
theorem not_complete :
    ¬ Filtered.Complete (generatedFilteredSpace alg) := by
  intro hcomplete
  rcases hcomplete factorialCombs factorialCombs_cauchy with ⟨x, hx⟩
  exact noLimit x hx

end OnePoint
end Resolution
