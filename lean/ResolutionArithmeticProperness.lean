import ResolutionFiniteBaseProperness

/-!
# Properness of the natural-arithmetic observational completion

The finite-base properness criterion does not apply to the natural-number
arithmetic algebra because its preserved old carrier is infinite.  This module
settles that example directly.

Start with the singular Answer `0 / 0` and repeatedly apply the old right
identity `x + 0`.  The generated syntax keeps every such application because
its left child is non-old.  In every preserving observer, however, `x + 0`
fixes every old state.  Only the finitely many fresh tags and overflow can move.
Consequently the factorially sampled orbit is Cauchy at every finite tag
budget.  A candidate-tailored preserving observer sends a sufficiently long
tail to absorbing overflow while retaining the candidate below overflow, so
the sequence has no generated limit.

The same mechanism also gives a small obstruction to stage-zero discreteness:
one and two applications of `+ 0` to `0 / 0` are distinct generated Answers,
but every zero-tag observer identifies them.
-/

namespace Resolution
namespace ArithmeticProperness

open Resolution.External
open Resolution.Orbit
open Resolution.External.FiniteTagProof
open Resolution.External.NatArithmetic

/-! ## The repeated-add-zero family -/

/-- Syntax for `0 / 0`, followed by `k` applications of right addition by
    zero. -/
def addZeroExpr : Nat -> Expr signature Nat
  | 0 => .app Op.div (.val 0) (.val 0)
  | k + 1 => .app Op.add (addZeroExpr k) (.val 0)

/-- The corresponding normalized raw Answer.  It is written explicitly so
    its unbounded syntactic growth is transparent. -/
def addZeroRaw : Nat -> RawAns signature Nat
  | 0 => .susp Op.div (.old 0) (.old 0)
  | k + 1 => .susp Op.add (addZeroRaw k) (.old 0)

theorem addZeroRaw_ne_old (k a : Nat) :
    addZeroRaw k ≠ (.old a : RawAns signature Nat) := by
  cases k <;> simp [addZeroRaw]

/-- Resolving the displayed expression gives exactly the displayed raw tree. -/
theorem res_addZeroExpr :
    forall k : Nat, Expr.res alg (addZeroExpr k) = addZeroRaw k
  | 0 => by
      simp [addZeroExpr, addZeroRaw, Expr.res, PartialAlg.liftOp,
        eval_div_zero]
  | k + 1 => by
      change alg.liftOp Op.add (Expr.res alg (addZeroExpr k)) (.old 0) =
        .susp Op.add (addZeroRaw k) (.old 0)
      rw [res_addZeroExpr k]
      cases h : addZeroRaw k with
      | old a => exact False.elim (addZeroRaw_ne_old k a h)
      | susp f l r => rfl

/-- The `k`th repeated-add-zero generated Answer. -/
def addZeroAnswer (k : Nat) : Free.GeneratedAns alg :=
  ⟨addZeroRaw k, ⟨addZeroExpr k, res_addZeroExpr k⟩⟩

@[simp] theorem addZeroAnswer_val (k : Nat) :
    (addZeroAnswer k).1 = addZeroRaw k := rfl

/-- Constructor count grows by two at every added-zero step. -/
theorem addZeroRaw_nodeCount :
    forall k : Nat, nodeCount alg (addZeroRaw k) = 2 * k + 3
  | 0 => rfl
  | k + 1 => by
      change 1 + (nodeCount alg (addZeroRaw k) + 1) = 2 * (k + 1) + 3
      rw [addZeroRaw_nodeCount k]
      omega

/-- Different iteration counts give different generated Answers. -/
theorem addZeroAnswer_injective : Function.Injective addZeroAnswer := by
  intro i j hij
  have hraw : addZeroRaw i = addZeroRaw j := congrArg Subtype.val hij
  have hcount := congrArg (nodeCount alg) hraw
  rw [addZeroRaw_nodeCount i, addZeroRaw_nodeCount j] at hcount
  omega

/-! ## Observer orbits modulo the pointwise-fixed old base -/

variable {n : Nat}

/-- Applying the arithmetic right identity inside one observer. -/
def observerStep (T : FiniteTagAlg alg n) :
    FiniteTagCarrier alg n -> FiniteTagCarrier alg n :=
  fun s => T.op Op.add s (Sum.inl 0)

/-- Every old state is fixed by the observer step because preservation pins
    ordinary addition. -/
theorem observerStep_old (T : FiniteTagAlg alg n) (a : Nat) :
    observerStep T (Sum.inl a) = Sum.inl a := by
  simpa [observerStep] using
    (T.preserve Op.add a 0 (a + 0) (eval_add a 0))

/-- Collapse the infinite old carrier to one settled state, retaining the
    finite complement exactly. -/
def collapse : FiniteTagCarrier alg n -> Orbit.TagState n
  | Sum.inl _ => Sum.inl ()
  | Sum.inr q => Sum.inr q

/-- The induced step on the finite quotient: once an orbit reaches the old
    carrier it remains settled. -/
def collapsedStep (T : FiniteTagAlg alg n) :
    Orbit.TagState n -> Orbit.TagState n
  | Sum.inl _ => Sum.inl ()
  | Sum.inr q => collapse (observerStep T (Sum.inr q))

theorem collapse_step (T : FiniteTagAlg alg n) :
    forall s : FiniteTagCarrier alg n,
      collapse (observerStep T s) = collapsedStep T (collapse s)
  | Sum.inl a => by rw [observerStep_old T a]; rfl
  | Sum.inr q => rfl

theorem collapse_orbit (T : FiniteTagAlg alg n)
    (s : FiniteTagCarrier alg n) :
    forall k : Nat,
      collapse (orb (observerStep T) s k) =
        orb (collapsedStep T) (collapse s) k
  | 0 => rfl
  | k + 1 => by
      rw [orb_succ, collapse_step T, collapse_orbit T s k]
      rfl

theorem observerOrbit_old (T : FiniteTagAlg alg n) (a : Nat) :
    forall k : Nat,
      orb (observerStep T) (Sum.inl a) k = Sum.inl a
  | 0 => rfl
  | k + 1 => by
      rw [orb_succ, observerOrbit_old T a k, observerStep_old T a]

/-- Equality in the collapsed orbit lifts back to the original orbit.  If the
    collapsed state is old, determinism and `x + 0 = x` show that both indices
    contain the same old value; complement states are retained injectively. -/
theorem observerOrbit_eq_of_collapse_eq
    (T : FiniteTagAlg alg n) (s : FiniteTagCarrier alg n)
    {i j : Nat} (hij : i <= j)
    (hc : collapse (orb (observerStep T) s i) =
      collapse (orb (observerStep T) s j)) :
    orb (observerStep T) s i = orb (observerStep T) s j := by
  cases hi : orb (observerStep T) s i with
  | inl a =>
      have hjform : j = i + (j - i) := by omega
      have hjold :
          orb (observerStep T) s j = Sum.inl a := by
        rw [hjform, orb_add, hi, observerOrbit_old]
      exact hjold.symm
  | inr q =>
      cases hj : orb (observerStep T) s j with
      | inl b =>
          simp [collapse, hi, hj] at hc
      | inr r =>
          have hqr : q = r := by simpa [collapse, hi, hj] using hc
          simpa [hqr]

/-- The infinite old base causes no orbit problem here: it is pointwise fixed,
    so only the `n` tags and overflow can support nontrivial motion. -/
theorem observerOrbit_eq_of_factorial_dvd
    (T : FiniteTagAlg alg n) (s : FiniteTagCarrier alg n)
    {i j : Nat} (hi : n + 2 <= i) (hij : i <= j)
    (hdvd : fact (n + 2) ∣ (j - i)) :
    orb (observerStep T) s i = orb (observerStep T) s j := by
  have hc :
      orb (collapsedStep T) (collapse s) i =
        orb (collapsedStep T) (collapse s) j :=
    orbit_eq_of_factorial_dvd
      (collapsedStep T) (collapse s) (tagCoded n) hi hij hdvd
  rw [← collapse_orbit T s i, ← collapse_orbit T s j] at hc
  exact observerOrbit_eq_of_collapse_eq T s hij hc

/-- Folding the repeated-add-zero tree is precisely the observer-step orbit
    starting at the interpretation of `0 / 0`. -/
theorem fold_addZero_eq_orbit (T : FiniteTagAlg alg n) :
    forall k : Nat,
      Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw k) =
        orb (observerStep T)
          (Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw 0)) k
  | 0 => rfl
  | k + 1 => by
      change T.op Op.add
          (Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw k))
          (Sum.inl 0) = _
      rw [fold_addZero_eq_orbit T k]
      rfl

/-- Past `n+2`, iteration indices congruent modulo `(n+2)!` agree in every
    stage-`n` observer. -/
theorem addZero_eqAt_of_factorial_dvd
    {i j : Nat} (hi : n + 2 <= i) (hij : i <= j)
    (hdvd : fact (n + 2) ∣ (j - i)) :
    FiniteTagEqAt alg n (addZeroAnswer i) (addZeroAnswer j) := by
  intro T
  show Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw i) =
    Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw j)
  rw [fold_addZero_eq_orbit T i, fold_addZero_eq_orbit T j]
  exact observerOrbit_eq_of_factorial_dvd T _ hi hij hdvd

/-! ## The arithmetic Cauchy sequence -/

/-- Factorially sampled repeated additions of zero to `0 / 0`. -/
def factorialAddZeros (k : Nat) : Free.GeneratedAns alg :=
  addZeroAnswer (fact k)

theorem factorialAddZeros_eqAt
    {i j : Nat} (hi : n + 2 <= i) (hj : n + 2 <= j) :
    FiniteTagEqAt alg n (factorialAddZeros i) (factorialAddZeros j) := by
  have hdi : fact (n + 2) ∣ fact i := fact_dvd_fact _ _ hi
  have hdj : fact (n + 2) ∣ fact j := fact_dvd_fact _ _ hj
  have hbi : n + 2 <= fact i := Nat.le_trans hi (le_fact i)
  have hbj : n + 2 <= fact j := Nat.le_trans hj (le_fact j)
  rcases Nat.le_total (fact i) (fact j) with hle | hle
  · exact addZero_eqAt_of_factorial_dvd hbi hle
      (FiniteBaseProperness.dvd_sub_of_dvd_of_dvd hdi hdj)
  · exact finiteTagEqAt_symm alg n
      (addZero_eqAt_of_factorial_dvd hbj hle
        (FiniteBaseProperness.dvd_sub_of_dvd_of_dvd hdj hdi))

/-- The arithmetic witness is Cauchy despite the infinite old carrier. -/
theorem factorialAddZeros_cauchy :
    Filtered.Cauchy (generatedFilteredSpace alg) factorialAddZeros := by
  intro m
  exact ⟨m + 2, fun i j hi hj => factorialAddZeros_eqAt hi hj⟩

/-! ## Stage zero is not separating -/

/-- On the zero-tag carrier, the right-add-zero observer step is idempotent. -/
theorem observerStep_idempotent_zero
    (T : FiniteTagAlg alg 0) (s : FiniteTagCarrier alg 0) :
    observerStep T (observerStep T s) = observerStep T s := by
  cases s with
  | inl a => rw [observerStep_old T a, observerStep_old T a]
  | inr q =>
      cases q with
      | inl i => exact Fin.elim0 i
      | inr u =>
          cases h : observerStep T (Sum.inr (Sum.inr u)) with
          | inl a => exact observerStep_old T a
          | inr q' =>
              cases q' with
              | inl i => exact Fin.elim0 i
              | inr u' =>
                  cases u
                  cases u'
                  exact h

/-- One and two applications of `+ 0` are observationally equal at stage zero. -/
theorem addZero_one_two_eqAt_zero :
    FiniteTagEqAt alg 0 (addZeroAnswer 1) (addZeroAnswer 2) := by
  intro T
  show Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw 1) =
    Free.TotalAlg.foldRaw alg (T.toTotalAlg alg) (addZeroRaw 2)
  rw [fold_addZero_eq_orbit T 1, fold_addZero_eq_orbit T 2]
  exact (observerStep_idempotent_zero T _).symm

/-- Stage-zero observation is strictly coarser than equality in the natural
    arithmetic generated algebra. -/
theorem stageZero_not_separating :
    exists x y : Free.GeneratedAns alg,
      x ≠ y ∧ FiniteTagEqAt alg 0 x y := by
  refine ⟨addZeroAnswer 1, addZeroAnswer 2, ?_, addZero_one_two_eqAt_zero⟩
  intro h
  have hij : (1 : Nat) = 2 := addZeroAnswer_injective h
  omega

/-! ## The Cauchy sequence has no generated limit -/

theorem old_zero_mem_addZero_subterms (k : Nat) :
    (.old 0 : RawAns signature Nat) ∈
      subterms alg (addZeroRaw (k + 1)) := by
  simp [addZeroRaw, subterms, self_mem_subterms]

/-- A repeated-add-zero tree one step beyond the chosen prefix cannot already
    occur in the finite subterm closure of the candidate and prefix. -/
theorem addZero_after_candidate_prefix_not_selected
    (x : RawAns signature Nat) :
    addZeroRaw (nodeCount alg x + 2) ∉
      selected alg x (addZeroRaw (nodeCount alg x + 1)) := by
  intro hmem
  simp only [selected, List.mem_append] at hmem
  rcases hmem with hx | hp
  · have hle := FiniteBaseProperness.nodeCount_le_of_mem_subterms alg hx
    have hcount := addZeroRaw_nodeCount (nodeCount alg x + 2)
    omega
  · have hle := FiniteBaseProperness.nodeCount_le_of_mem_subterms alg hp
    have hnext := addZeroRaw_nodeCount (nodeCount alg x + 2)
    have hpref := addZeroRaw_nodeCount (nodeCount alg x + 1)
    omega

/-- Immediately after the candidate-sized prefix, the selected finite table
    deliberately misses and returns overflow. -/
theorem table_after_candidate_prefix
    (x : RawAns signature Nat) :
    table alg x (addZeroRaw (nodeCount alg x + 1)) Op.add
        (encode alg x (addZeroRaw (nodeCount alg x + 1))
          (addZeroRaw (nodeCount alg x + 1)))
        (encode alg x (addZeroRaw (nodeCount alg x + 1)) (.old 0)) =
      overflow alg := by
  classical
  let p := addZeroRaw (nodeCount alg x + 1)
  have hpRoot : p ∈ selected alg x p :=
    right_root_mem_selected alg x p
  have hzSub : (.old 0 : RawAns signature Nat) ∈ subterms alg p := by
    exact old_zero_mem_addZero_subterms (nodeCount alg x)
  have hzSel : (.old 0 : RawAns signature Nat) ∈ selected alg x p := by
    simp [selected, hzSub]
  have hnext : addZeroRaw (nodeCount alg x + 2) ∉ selected alg x p := by
    exact addZero_after_candidate_prefix_not_selected x
  have hnone : ¬(Exists fun s : RawAns signature Nat =>
      s ∈ selected alg x p ∧
        MatchNode alg x p Op.add (encode alg x p p)
          (encode alg x p (.old 0)) s) := by
    rintro ⟨s, hs, hm⟩
    cases s with
    | old b =>
        simp [MatchNode] at hm
    | susp g l r =>
        have hc := children_mem_selected alg hs
        have hm0 := hm
        simp only [MatchNode] at hm0
        have hm' : g = Op.add ∧ encode alg x p l = encode alg x p p ∧
            encode alg x p r = encode alg x p (.old 0) := hm0
        have hl : l = p := encode_injective_on alg hc.1 hpRoot hm'.2.1
        have hr : r = .old 0 := encode_injective_on alg hc.2 hzSel hm'.2.2
        have hsNext : RawAns.susp g l r =
            addZeroRaw (nodeCount alg x + 2) := by
          change RawAns.susp g l r =
            RawAns.susp Op.add (addZeroRaw (nodeCount alg x + 1)) (.old 0)
          cases hm'.1
          cases hl
          cases hr
          rfl
        exact hnext (hsNext ▸ hs)
  change table alg x p Op.add (encode alg x p p)
      (encode alg x p (.old 0)) = overflow alg
  simp only [table, dif_neg hnone]

theorem finiteOp_after_candidate_prefix
    (x : RawAns signature Nat) :
    finiteOp alg x (addZeroRaw (nodeCount alg x + 1)) Op.add
        (encode alg x (addZeroRaw (nodeCount alg x + 1))
          (addZeroRaw (nodeCount alg x + 1)))
        (encode alg x (addZeroRaw (nodeCount alg x + 1)) (.old 0)) =
      overflow alg := by
  let p := addZeroRaw (nodeCount alg x + 1)
  have hpRoot : p ∈ selected alg x p := right_root_mem_selected alg x p
  have hpShape : p = .susp Op.add
      (addZeroRaw (nodeCount alg x)) (.old 0) := by rfl
  change finiteOp alg x p Op.add (encode alg x p p)
      (encode alg x p (.old 0)) = overflow alg
  cases hpCase : p with
  | old b =>
      rw [hpCase] at hpShape
      cases hpShape
  | susp g l r =>
      have hsRoot : RawAns.susp g l r ∈
          selected alg x (RawAns.susp g l r) :=
        right_root_mem_selected alg x (RawAns.susp g l r)
      have henc : encode alg x (RawAns.susp g l r) (RawAns.susp g l r) =
          (Sum.inr (Sum.inl
            (tagIndex (RawAns.susp g l r)
              (selected alg x (RawAns.susp g l r)) hsRoot)) :
                FiniteTagCarrier alg
                  (selected alg x (RawAns.susp g l r)).length) :=
        encode_susp_of_mem alg hsRoot
      rw [henc]
      change table alg x (RawAns.susp g l r) Op.add
          (Sum.inr (Sum.inl
            (tagIndex (RawAns.susp g l r)
              (selected alg x (RawAns.susp g l r)) hsRoot)))
          (encode alg x (RawAns.susp g l r) (.old 0)) = overflow alg
      have htable := table_after_candidate_prefix x
      change table alg x p Op.add (encode alg x p p)
          (encode alg x p (.old 0)) = overflow alg at htable
      rw [hpCase] at htable
      rw [henc] at htable
      exact htable

/-- The candidate-tailored observer evaluates the retained prefix to its
    selected tag. -/
theorem fold_candidate_prefix_eq_encode
    (x : RawAns signature Nat) :
    let p := addZeroRaw (nodeCount alg x + 1)
    Free.TotalAlg.foldRaw alg ((separatingAlg alg x p).toTotalAlg alg) p =
      encode alg x p p := by
  let p := addZeroRaw (nodeCount alg x + 1)
  have hpNormal : Normal alg p := by
    change Normal alg (addZeroRaw (nodeCount alg x + 1))
    rw [← res_addZeroExpr (nodeCount alg x + 1)]
    exact res_normal alg (addZeroExpr (nodeCount alg x + 1))
  exact foldRaw_eq_encode alg p (right_root_mem_selected alg x p) hpNormal

/-- The next iteration enters overflow. -/
theorem fold_candidate_next_eq_overflow
    (x : RawAns signature Nat) :
    let p := addZeroRaw (nodeCount alg x + 1)
    Free.TotalAlg.foldRaw alg ((separatingAlg alg x p).toTotalAlg alg)
        (addZeroRaw (nodeCount alg x + 2)) = overflow alg := by
  let p := addZeroRaw (nodeCount alg x + 1)
  change finiteOp alg x p Op.add
      (Free.TotalAlg.foldRaw alg ((separatingAlg alg x p).toTotalAlg alg) p)
      (Sum.inl 0) = overflow alg
  rw [fold_candidate_prefix_eq_encode x]
  simpa only [encode] using finiteOp_after_candidate_prefix x

/-- Once overflow is reached, every longer repeated-add-zero tree remains
    there in the candidate-tailored observer. -/
theorem fold_candidate_tail_eq_overflow
    (x : RawAns signature Nat) :
    let p := addZeroRaw (nodeCount alg x + 1)
    forall d : Nat,
      Free.TotalAlg.foldRaw alg ((separatingAlg alg x p).toTotalAlg alg)
          (addZeroRaw (nodeCount alg x + 2 + d)) = overflow alg := by
  let p := addZeroRaw (nodeCount alg x + 1)
  change forall d : Nat,
    Free.TotalAlg.foldRaw alg ((separatingAlg alg x p).toTotalAlg alg)
      (addZeroRaw (nodeCount alg x + 2 + d)) = overflow alg
  intro d
  induction d with
  | zero => simpa using fold_candidate_next_eq_overflow x
  | succ d ih =>
      have hindex : nodeCount alg x + 2 + (d + 1) =
          (nodeCount alg x + 2 + d) + 1 := by omega
      rw [hindex]
      change finiteOp alg x p Op.add
          (Free.TotalAlg.foldRaw alg ((separatingAlg alg x p).toTotalAlg alg)
            (addZeroRaw (nodeCount alg x + 2 + d)))
          (Sum.inl 0) = overflow alg
      rw [ih]
      exact FiniteBaseProperness.finiteOp_overflow_left
        alg x p Op.add (Sum.inl 0)

/-- The factorial repeated-add-zero sequence has no generated limit. -/
theorem factorialAddZeros_noLimit (x : Free.GeneratedAns alg) :
    ¬ Filtered.Converges (generatedFilteredSpace alg) factorialAddZeros x := by
  intro hconv
  let p := addZeroRaw (nodeCount alg x.1 + 1)
  let stage := (selected alg x.1 p).length
  rcases hconv stage with ⟨N, hN⟩
  let K := N + nodeCount alg x.1 + 2
  have hNK : N <= K := by omega
  have hlarge : nodeCount alg x.1 + 2 <= fact K := by
    have hKfact := le_fact K
    omega
  have hindex : nodeCount alg x.1 + 2 +
      (fact K - (nodeCount alg x.1 + 2)) = fact K := by omega
  have hxNormal : Normal alg x.1 := by
    rcases x.2 with ⟨e, he⟩
    rw [← he]
    exact res_normal alg e
  have hxMem : x.1 ∈ selected alg x.1 p :=
    left_root_mem_selected alg x.1 p
  have hxFold :
      Free.TotalAlg.foldRaw alg ((separatingAlg alg x.1 p).toTotalAlg alg) x.1 =
        encode alg x.1 p x.1 :=
    foldRaw_eq_encode alg x.1 hxMem hxNormal
  have htail :
      Free.TotalAlg.foldRaw alg ((separatingAlg alg x.1 p).toTotalAlg alg)
          (addZeroRaw (fact K)) = overflow alg := by
    rw [← hindex]
    exact fold_candidate_tail_eq_overflow x.1
      (fact K - (nodeCount alg x.1 + 2))
  have hmodel := hN K hNK (separatingAlg alg x.1 p)
  change Free.TotalAlg.foldRaw alg
      ((separatingAlg alg x.1 p).toTotalAlg alg) x.1 =
    Free.TotalAlg.foldRaw alg
      ((separatingAlg alg x.1 p).toTotalAlg alg)
      (addZeroRaw (fact K)) at hmodel
  rw [hxFold, htail] at hmodel
  exact (FiniteBaseProperness.encode_ne_overflow_of_mem alg hxMem) hmodel

/-- Natural-number arithmetic is not complete for finite-tag observation. -/
theorem not_complete :
    ¬ Filtered.Complete (generatedFilteredSpace alg) := by
  intro hcomplete
  rcases hcomplete factorialAddZeros factorialAddZeros_cauchy with ⟨x, hx⟩
  exact factorialAddZeros_noLimit x hx

/-! ## No finite stage is equality -/

theorem fact_succ_strict {k : Nat} (hk : 1 <= k) :
    fact k < fact (k + 1) := by
  change fact k < (k + 1) * fact k
  have hp := fact_pos k
  calc
    fact k < 2 * fact k := by omega
    _ <= (k + 1) * fact k :=
      Nat.mul_le_mul_right (fact k) (by omega)

/-- At every finite observation budget there remain two distinct arithmetic
    Answers which that whole stage cannot distinguish. -/
theorem every_stage_not_equality (m : Nat) :
    exists x y : Free.GeneratedAns alg,
      x ≠ y ∧ FiniteTagEqAt alg m x y := by
  refine ⟨factorialAddZeros (m + 2), factorialAddZeros (m + 3), ?_, ?_⟩
  · intro h
    have hindex : fact (m + 2) = fact (m + 3) :=
      addZeroAnswer_injective h
    have hstrict : fact (m + 2) < fact (m + 3) := by
      exact fact_succ_strict (by omega)
    omega
  · exact factorialAddZeros_eqAt (by omega) (by omega)

/-! ## An explicit new completion point -/

def factorialAddZerosCauchySeq :
    Filtered.CauchySeq (generatedFilteredSpace alg) where
  term := factorialAddZeros
  cauchy := factorialAddZeros_cauchy

def completionWitness :
    Filtered.Completion (generatedFilteredSpace alg) :=
  Filtered.classOf (generatedFilteredSpace alg) factorialAddZerosCauchySeq

theorem completionWitness_ne_embed (x : Free.GeneratedAns alg) :
    completionWitness ≠ Filtered.embed (generatedFilteredSpace alg) x := by
  intro h
  apply factorialAddZeros_noLimit x
  have hclass :
      Filtered.classOf (generatedFilteredSpace alg) factorialAddZerosCauchySeq =
        Filtered.embed (generatedFilteredSpace alg) x := by
    simpa [completionWitness] using h
  have hconv :=
    (Filtered.classOf_eq_embed_iff
      (generatedFilteredSpace alg) factorialAddZerosCauchySeq x).1 hclass
  simpa [factorialAddZerosCauchySeq] using hconv

/-- The natural-arithmetic completion embedding is not surjective. -/
theorem completionEmbedding_not_surjective :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace alg)) := by
  intro hsurj
  rcases hsurj completionWitness with ⟨x, hx⟩
  exact completionWitness_ne_embed x hx.symm

/-- The natural-arithmetic observational completion contains an explicit point
    outside the image of every finite generated Answer. -/
theorem completion_adds_point :
    exists q : Filtered.Completion (generatedFilteredSpace alg),
      forall x : Free.GeneratedAns alg,
        Filtered.embed (generatedFilteredSpace alg) x ≠ q := by
  refine ⟨completionWitness, ?_⟩
  intro x
  exact Ne.symm (completionWitness_ne_embed x)

end ArithmeticProperness
end Resolution
