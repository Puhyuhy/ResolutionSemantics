import ResolutionFiniteBaseProperness

/-!
# Properness from an old-fixing unary context

This module isolates the mechanism behind the natural-arithmetic properness
witness.  No finiteness assumption is made on the old carrier.

Suppose a partial algebra has one undefined old application and a binary
operation with a fixed old right argument that acts as the identity on every
old element.  Start at the unresolved application and repeatedly apply that
old-fixing context.  Generated syntax grows at every step.  In any preserving
stage-`n` observer, however, all old states are fixed, so the infinite old
carrier may be collapsed to one settled state while retaining the `n` tags and
overflow exactly.  Factorial sampling is therefore Cauchy.

A candidate-tailored preserving observer retains a finite prefix and sends the
next iterate to absorbing overflow.  Hence the factorial sequence has no
generated limit, every finite observation stage is strictly coarser than
equality, and the completion embedding is not surjective.
-/

universe u v

namespace Resolution

variable {Sigma : Signature.{u}}

/-- Data witnessing an undefined old application together with a unary
    context `x ↦ stepOp x fixedRight` that fixes the old carrier pointwise. -/
structure OldFixingContextWitness
    (D : PartialAlg.{u,v} Sigma) where
  seedOp : Sigma.Op
  seedLeft : D.Carrier
  seedRight : D.Carrier
  seedUndefined : D.eval seedOp seedLeft seedRight = none
  stepOp : Sigma.Op
  fixedRight : D.Carrier
  fixesOld : forall a : D.Carrier,
    D.eval stepOp a fixedRight = some a

namespace OldFixingContextProperness

open Resolution.External
open Resolution.Orbit
open Resolution.External.FiniteTagProof

variable (D : PartialAlg.{u,v} Sigma)
variable (W : OldFixingContextWitness D)

/-! ## Iterating the old-fixing context -/

/-- The undefined seed followed by `k` applications of the old-fixing
    context. -/
def iterateExpr : Nat -> Expr Sigma D.Carrier
  | 0 => .app W.seedOp (.val W.seedLeft) (.val W.seedRight)
  | k + 1 => .app W.stepOp (iterateExpr k) (.val W.fixedRight)

/-- The corresponding normalized raw Answer. -/
def iterateRaw : Nat -> RawAns Sigma D.Carrier
  | 0 => .susp W.seedOp (.old W.seedLeft) (.old W.seedRight)
  | k + 1 => .susp W.stepOp (iterateRaw k) (.old W.fixedRight)

theorem iterateRaw_ne_old (k : Nat) (a : D.Carrier) :
    iterateRaw D W k ≠ (.old a : RawAns Sigma D.Carrier) := by
  cases k <;> simp [iterateRaw]

/-- Resolving the displayed expression gives the displayed raw tree. -/
theorem res_iterateExpr :
    forall k : Nat, Expr.res D (iterateExpr D W k) = iterateRaw D W k
  | 0 => by
      simp [iterateExpr, iterateRaw, Expr.res, PartialAlg.liftOp,
        W.seedUndefined]
  | k + 1 => by
      change D.liftOp W.stepOp (Expr.res D (iterateExpr D W k))
          (.old W.fixedRight) =
        .susp W.stepOp (iterateRaw D W k) (.old W.fixedRight)
      rw [res_iterateExpr k]
      cases h : iterateRaw D W k with
      | old a => exact False.elim (iterateRaw_ne_old D W k a h)
      | susp f l r => rfl

/-- The `k`th generated Answer in the old-fixing orbit. -/
def iterateAnswer (k : Nat) : Free.GeneratedAns D :=
  ⟨iterateRaw D W k, ⟨iterateExpr D W k, res_iterateExpr D W k⟩⟩

@[simp] theorem iterateAnswer_val (k : Nat) :
    (iterateAnswer D W k).1 = iterateRaw D W k := rfl

/-- Constructor count grows by two at every context application. -/
theorem iterateRaw_nodeCount :
    forall k : Nat, nodeCount D (iterateRaw D W k) = 2 * k + 3
  | 0 => rfl
  | k + 1 => by
      change 1 + (nodeCount D (iterateRaw D W k) + 1) =
        2 * (k + 1) + 3
      rw [iterateRaw_nodeCount k]
      omega

/-- Different iteration counts give different generated Answers. -/
theorem iterateAnswer_injective : Function.Injective (iterateAnswer D W) := by
  intro i j hij
  have hraw : iterateRaw D W i = iterateRaw D W j :=
    congrArg Subtype.val hij
  have hcount := congrArg (nodeCount D) hraw
  rw [iterateRaw_nodeCount D W i, iterateRaw_nodeCount D W j] at hcount
  omega

/-! ## Observer orbits modulo the pointwise-fixed old base -/

variable {n : Nat}

/-- Applying the old-fixing context inside one observer. -/
def observerStep (T : FiniteTagAlg D n) :
    FiniteTagCarrier D n -> FiniteTagCarrier D n :=
  fun s => T.op W.stepOp s (Sum.inl W.fixedRight)

/-- Preservation makes every old state a fixed point of the observer step. -/
theorem observerStep_old (T : FiniteTagAlg D n) (a : D.Carrier) :
    observerStep D W T (Sum.inl a) = Sum.inl a := by
  simpa [observerStep] using
    (T.preserve W.stepOp a W.fixedRight a (W.fixesOld a))

/-- Collapse the possibly infinite old carrier to one settled state while
    retaining the finite complement exactly. -/
def collapse : FiniteTagCarrier D n -> Orbit.TagState n
  | Sum.inl _ => Sum.inl ()
  | Sum.inr q => Sum.inr q

/-- The observer step induced on the finite quotient. -/
def collapsedStep (T : FiniteTagAlg D n) :
    Orbit.TagState n -> Orbit.TagState n
  | Sum.inl _ => Sum.inl ()
  | Sum.inr q => collapse D (observerStep D W T (Sum.inr q))

theorem collapse_step (T : FiniteTagAlg D n) :
    forall s : FiniteTagCarrier D n,
      collapse D (observerStep D W T s) =
        collapsedStep D W T (collapse D s)
  | Sum.inl a => by rw [observerStep_old D W T a]; rfl
  | Sum.inr q => rfl

theorem collapse_orbit (T : FiniteTagAlg D n)
    (s : FiniteTagCarrier D n) :
    forall k : Nat,
      collapse D (orb (observerStep D W T) s k) =
        orb (collapsedStep D W T) (collapse D s) k
  | 0 => rfl
  | k + 1 => by
      rw [orb_succ, collapse_step D W T, collapse_orbit T s k]
      rfl

theorem observerOrbit_old (T : FiniteTagAlg D n) (a : D.Carrier) :
    forall k : Nat,
      orb (observerStep D W T) (Sum.inl a) k = Sum.inl a
  | 0 => rfl
  | k + 1 => by
      rw [orb_succ, observerOrbit_old T a k,
        observerStep_old D W T a]

/-- Equality after collapse lifts back to the original orbit.  If the orbit
    has reached an old value, the old-fixing law preserves that exact value
    forever; complement states are retained injectively by `collapse`. -/
theorem observerOrbit_eq_of_collapse_eq
    (T : FiniteTagAlg D n) (s : FiniteTagCarrier D n)
    {i j : Nat} (hij : i <= j)
    (hc : collapse D (orb (observerStep D W T) s i) =
      collapse D (orb (observerStep D W T) s j)) :
    orb (observerStep D W T) s i = orb (observerStep D W T) s j := by
  cases hi : orb (observerStep D W T) s i with
  | inl a =>
      have hjform : j = i + (j - i) := by omega
      have hjold : orb (observerStep D W T) s j = Sum.inl a := by
        rw [hjform, orb_add, hi, observerOrbit_old D W T]
      exact hjold.symm
  | inr q =>
      cases hj : orb (observerStep D W T) s j with
      | inl b =>
          simp [collapse, hi, hj] at hc
      | inr r =>
          have hqr : q = r := by simpa [collapse, hi, hj] using hc
          simpa [hqr]

/-- Only the `n` fresh tags and overflow can support nontrivial motion, even
    when the pointwise-fixed old carrier is infinite. -/
theorem observerOrbit_eq_of_factorial_dvd
    (T : FiniteTagAlg D n) (s : FiniteTagCarrier D n)
    {i j : Nat} (hi : n + 2 <= i) (hij : i <= j)
    (hdvd : fact (n + 2) ∣ (j - i)) :
    orb (observerStep D W T) s i = orb (observerStep D W T) s j := by
  have hc :
      orb (collapsedStep D W T) (collapse D s) i =
        orb (collapsedStep D W T) (collapse D s) j :=
    orbit_eq_of_factorial_dvd
      (collapsedStep D W T) (collapse D s) (tagCoded n) hi hij hdvd
  rw [← collapse_orbit D W T s i, ← collapse_orbit D W T s j] at hc
  exact observerOrbit_eq_of_collapse_eq D W T s hij hc

/-- Folding an iterate is the observer-step orbit from the unresolved seed. -/
theorem fold_iterate_eq_orbit (T : FiniteTagAlg D n) :
    forall k : Nat,
      Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W k) =
        orb (observerStep D W T)
          (Free.TotalAlg.foldRaw D (T.toTotalAlg D)
            (iterateRaw D W 0)) k
  | 0 => rfl
  | k + 1 => by
      change T.op W.stepOp
          (Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W k))
          (Sum.inl W.fixedRight) = _
      rw [fold_iterate_eq_orbit T k]
      rfl

/-- Past `n+2`, iteration indices congruent modulo `(n+2)!` agree in every
    stage-`n` observer. -/
theorem iterate_eqAt_of_factorial_dvd
    {i j : Nat} (hi : n + 2 <= i) (hij : i <= j)
    (hdvd : fact (n + 2) ∣ (j - i)) :
    FiniteTagEqAt D n (iterateAnswer D W i) (iterateAnswer D W j) := by
  intro T
  show Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W i) =
    Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W j)
  rw [fold_iterate_eq_orbit D W T i, fold_iterate_eq_orbit D W T j]
  exact observerOrbit_eq_of_factorial_dvd D W T _ hi hij hdvd

/-! ## The factorial Cauchy sequence -/

/-- Factorially sampled iterates of the old-fixing context. -/
def factorialIterates (k : Nat) : Free.GeneratedAns D :=
  iterateAnswer D W (fact k)

theorem factorialIterates_eqAt
    {i j : Nat} (hi : n + 2 <= i) (hj : n + 2 <= j) :
    FiniteTagEqAt D n (factorialIterates D W i)
      (factorialIterates D W j) := by
  have hdi : fact (n + 2) ∣ fact i := fact_dvd_fact _ _ hi
  have hdj : fact (n + 2) ∣ fact j := fact_dvd_fact _ _ hj
  have hbi : n + 2 <= fact i := Nat.le_trans hi (le_fact i)
  have hbj : n + 2 <= fact j := Nat.le_trans hj (le_fact j)
  rcases Nat.le_total (fact i) (fact j) with hle | hle
  · exact iterate_eqAt_of_factorial_dvd D W hbi hle
      (FiniteBaseProperness.dvd_sub_of_dvd_of_dvd hdi hdj)
  · exact finiteTagEqAt_symm D n
      (iterate_eqAt_of_factorial_dvd D W hbj hle
        (FiniteBaseProperness.dvd_sub_of_dvd_of_dvd hdj hdi))

/-- The factorial orbit is Cauchy with no finiteness assumption on the base. -/
theorem factorialIterates_cauchy :
    Filtered.Cauchy (generatedFilteredSpace D) (factorialIterates D W) := by
  intro m
  exact ⟨m + 2, fun i j hi hj =>
    factorialIterates_eqAt D W hi hj⟩

/-! ## Stage zero and all finite stages are non-discrete -/

/-- With no fresh tags, a step fixing all old states is idempotent. -/
theorem observerStep_idempotent_zero
    (T : FiniteTagAlg D 0) (s : FiniteTagCarrier D 0) :
    observerStep D W T (observerStep D W T s) =
      observerStep D W T s := by
  cases s with
  | inl a => rw [observerStep_old D W T a, observerStep_old D W T a]
  | inr q =>
      cases q with
      | inl i => exact Fin.elim0 i
      | inr u0 =>
          cases h : observerStep D W T (Sum.inr (Sum.inr u0)) with
          | inl a => exact observerStep_old D W T a
          | inr q' =>
              cases q' with
              | inl i => exact Fin.elim0 i
              | inr u1 =>
                  cases u0
                  cases u1
                  exact h

theorem iterate_one_two_eqAt_zero :
    FiniteTagEqAt D 0 (iterateAnswer D W 1) (iterateAnswer D W 2) := by
  intro T
  show Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W 1) =
    Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W 2)
  rw [fold_iterate_eq_orbit D W T 1, fold_iterate_eq_orbit D W T 2]
  exact (observerStep_idempotent_zero D W T _).symm

/-- Stage zero is strictly coarser than equality. -/
theorem stageZero_not_separating (W : OldFixingContextWitness D) :
    exists x y : Free.GeneratedAns D,
      x ≠ y ∧ FiniteTagEqAt D 0 x y := by
  refine ⟨iterateAnswer D W 1, iterateAnswer D W 2, ?_,
    iterate_one_two_eqAt_zero D W⟩
  intro h
  have hij : (1 : Nat) = 2 := iterateAnswer_injective D W h
  omega

/-! ## The factorial sequence has no generated limit -/

theorem old_fixedRight_mem_iterate_subterms (k : Nat) :
    (.old W.fixedRight : RawAns Sigma D.Carrier) ∈
      subterms D (iterateRaw D W (k + 1)) := by
  simp [iterateRaw, subterms, self_mem_subterms]

/-- The next iterate is larger than every subtree of the candidate and the
    retained prefix, hence is not selected. -/
theorem iterate_after_candidate_prefix_not_selected
    (x : RawAns Sigma D.Carrier) :
    iterateRaw D W (nodeCount D x + 2) ∉
      selected D x (iterateRaw D W (nodeCount D x + 1)) := by
  intro hmem
  simp only [selected, List.mem_append] at hmem
  rcases hmem with hx | hp
  · have hle := FiniteBaseProperness.nodeCount_le_of_mem_subterms D hx
    have hcount := iterateRaw_nodeCount D W (nodeCount D x + 2)
    omega
  · have hle := FiniteBaseProperness.nodeCount_le_of_mem_subterms D hp
    have hnext := iterateRaw_nodeCount D W (nodeCount D x + 2)
    have hpref := iterateRaw_nodeCount D W (nodeCount D x + 1)
    omega

/-- The finite selected table misses immediately beyond the retained prefix. -/
theorem table_after_candidate_prefix
    (x : RawAns Sigma D.Carrier) :
    table D x (iterateRaw D W (nodeCount D x + 1)) W.stepOp
        (encode D x (iterateRaw D W (nodeCount D x + 1))
          (iterateRaw D W (nodeCount D x + 1)))
        (encode D x (iterateRaw D W (nodeCount D x + 1))
          (.old W.fixedRight)) =
      overflow D := by
  classical
  let p := iterateRaw D W (nodeCount D x + 1)
  have hpRoot : p ∈ selected D x p := right_root_mem_selected D x p
  have hzSub : (.old W.fixedRight : RawAns Sigma D.Carrier) ∈
      subterms D p := by
    exact old_fixedRight_mem_iterate_subterms D W (nodeCount D x)
  have hzSel : (.old W.fixedRight : RawAns Sigma D.Carrier) ∈
      selected D x p := by
    simp [selected, hzSub]
  have hnext : iterateRaw D W (nodeCount D x + 2) ∉ selected D x p := by
    exact iterate_after_candidate_prefix_not_selected D W x
  have hnone : ¬(Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected D x p ∧
        MatchNode D x p W.stepOp (encode D x p p)
          (encode D x p (.old W.fixedRight)) s) := by
    rintro ⟨s, hs, hm⟩
    cases s with
    | old b =>
        simp [MatchNode] at hm
    | susp g l r =>
        have hc := children_mem_selected D hs
        have hm0 := hm
        simp only [MatchNode] at hm0
        have hm' : g = W.stepOp ∧ encode D x p l = encode D x p p ∧
            encode D x p r = encode D x p (.old W.fixedRight) := hm0
        have hl : l = p := encode_injective_on D hc.1 hpRoot hm'.2.1
        have hr : r = .old W.fixedRight :=
          encode_injective_on D hc.2 hzSel hm'.2.2
        have hsNext : RawAns.susp g l r =
            iterateRaw D W (nodeCount D x + 2) := by
          change RawAns.susp g l r =
            RawAns.susp W.stepOp
              (iterateRaw D W (nodeCount D x + 1)) (.old W.fixedRight)
          cases hm'.1
          cases hl
          cases hr
          rfl
        exact hnext (hsNext ▸ hs)
  change table D x p W.stepOp (encode D x p p)
      (encode D x p (.old W.fixedRight)) = overflow D
  simp only [table, dif_neg hnone]

theorem finiteOp_after_candidate_prefix
    (x : RawAns Sigma D.Carrier) :
    finiteOp D x (iterateRaw D W (nodeCount D x + 1)) W.stepOp
        (encode D x (iterateRaw D W (nodeCount D x + 1))
          (iterateRaw D W (nodeCount D x + 1)))
        (encode D x (iterateRaw D W (nodeCount D x + 1))
          (.old W.fixedRight)) =
      overflow D := by
  let p := iterateRaw D W (nodeCount D x + 1)
  have hpRoot : p ∈ selected D x p := right_root_mem_selected D x p
  have hpShape : p = .susp W.stepOp
      (iterateRaw D W (nodeCount D x)) (.old W.fixedRight) := by rfl
  change finiteOp D x p W.stepOp (encode D x p p)
      (encode D x p (.old W.fixedRight)) = overflow D
  cases hpCase : p with
  | old b =>
      rw [hpCase] at hpShape
      cases hpShape
  | susp g l r =>
      have hsRoot : RawAns.susp g l r ∈
          selected D x (RawAns.susp g l r) :=
        right_root_mem_selected D x (RawAns.susp g l r)
      have henc : encode D x (RawAns.susp g l r)
          (RawAns.susp g l r) =
          (Sum.inr (Sum.inl
            (tagIndex (RawAns.susp g l r)
              (selected D x (RawAns.susp g l r)) hsRoot)) :
                FiniteTagCarrier D
                  (selected D x (RawAns.susp g l r)).length) :=
        encode_susp_of_mem D hsRoot
      rw [henc]
      change table D x (RawAns.susp g l r) W.stepOp
          (Sum.inr (Sum.inl
            (tagIndex (RawAns.susp g l r)
              (selected D x (RawAns.susp g l r)) hsRoot)))
          (encode D x (RawAns.susp g l r) (.old W.fixedRight)) = overflow D
      have htable := table_after_candidate_prefix D W x
      change table D x p W.stepOp (encode D x p p)
          (encode D x p (.old W.fixedRight)) = overflow D at htable
      rw [hpCase] at htable
      rw [henc] at htable
      exact htable

/-- The tailored observer evaluates the retained prefix to its selected tag. -/
theorem fold_candidate_prefix_eq_encode
    (x : RawAns Sigma D.Carrier) :
    let p := iterateRaw D W (nodeCount D x + 1)
    Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D) p =
      encode D x p p := by
  let p := iterateRaw D W (nodeCount D x + 1)
  have hpNormal : Normal D p := by
    change Normal D (iterateRaw D W (nodeCount D x + 1))
    rw [← res_iterateExpr D W (nodeCount D x + 1)]
    exact res_normal D (iterateExpr D W (nodeCount D x + 1))
  exact foldRaw_eq_encode D p (right_root_mem_selected D x p) hpNormal

/-- The next iterate enters overflow. -/
theorem fold_candidate_next_eq_overflow
    (x : RawAns Sigma D.Carrier) :
    let p := iterateRaw D W (nodeCount D x + 1)
    Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
        (iterateRaw D W (nodeCount D x + 2)) = overflow D := by
  let p := iterateRaw D W (nodeCount D x + 1)
  change finiteOp D x p W.stepOp
      (Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D) p)
      (Sum.inl W.fixedRight) = overflow D
  rw [fold_candidate_prefix_eq_encode D W x]
  simpa only [encode] using finiteOp_after_candidate_prefix D W x

/-- Once overflow is reached, all longer iterates remain there. -/
theorem fold_candidate_tail_eq_overflow
    (x : RawAns Sigma D.Carrier) :
    let p := iterateRaw D W (nodeCount D x + 1)
    forall d : Nat,
      Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
          (iterateRaw D W (nodeCount D x + 2 + d)) = overflow D := by
  let p := iterateRaw D W (nodeCount D x + 1)
  change forall d : Nat,
    Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
      (iterateRaw D W (nodeCount D x + 2 + d)) = overflow D
  intro d
  induction d with
  | zero => simpa using fold_candidate_next_eq_overflow D W x
  | succ d ih =>
      have hindex : nodeCount D x + 2 + (d + 1) =
          (nodeCount D x + 2 + d) + 1 := by omega
      rw [hindex]
      change finiteOp D x p W.stepOp
          (Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
            (iterateRaw D W (nodeCount D x + 2 + d)))
          (Sum.inl W.fixedRight) = overflow D
      rw [ih]
      exact FiniteBaseProperness.finiteOp_overflow_left
        D x p W.stepOp (Sum.inl W.fixedRight)

/-- The factorial orbit has no generated limit. -/
theorem factorialIterates_noLimit (x : Free.GeneratedAns D) :
    ¬ Filtered.Converges (generatedFilteredSpace D)
      (factorialIterates D W) x := by
  intro hconv
  let p := iterateRaw D W (nodeCount D x.1 + 1)
  let stage := (selected D x.1 p).length
  rcases hconv stage with ⟨N, hN⟩
  let K := N + nodeCount D x.1 + 2
  have hNK : N <= K := by omega
  have hlarge : nodeCount D x.1 + 2 <= fact K := by
    have hKfact := le_fact K
    omega
  have hindex : nodeCount D x.1 + 2 +
      (fact K - (nodeCount D x.1 + 2)) = fact K := by omega
  have hxNormal : Normal D x.1 := by
    rcases x.2 with ⟨e, he⟩
    rw [← he]
    exact res_normal D e
  have hxMem : x.1 ∈ selected D x.1 p :=
    left_root_mem_selected D x.1 p
  have hxFold :
      Free.TotalAlg.foldRaw D ((separatingAlg D x.1 p).toTotalAlg D) x.1 =
        encode D x.1 p x.1 :=
    foldRaw_eq_encode D x.1 hxMem hxNormal
  have htail :
      Free.TotalAlg.foldRaw D ((separatingAlg D x.1 p).toTotalAlg D)
          (iterateRaw D W (fact K)) = overflow D := by
    rw [← hindex]
    exact fold_candidate_tail_eq_overflow D W x.1
      (fact K - (nodeCount D x.1 + 2))
  have hmodel := hN K hNK (separatingAlg D x.1 p)
  change Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 p).toTotalAlg D) x.1 =
    Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 p).toTotalAlg D)
      (iterateRaw D W (fact K)) at hmodel
  rw [hxFold, htail] at hmodel
  exact (FiniteBaseProperness.encode_ne_overflow_of_mem D hxMem) hmodel

/-- The generated filtered space is not complete. -/
theorem not_complete (W : OldFixingContextWitness D) :
    ¬ Filtered.Complete (generatedFilteredSpace D) := by
  intro hcomplete
  rcases hcomplete (factorialIterates D W) (factorialIterates_cauchy D W) with
    ⟨x, hx⟩
  exact factorialIterates_noLimit D W x hx

theorem fact_succ_strict {k : Nat} (hk : 1 <= k) :
    fact k < fact (k + 1) := by
  change fact k < (k + 1) * fact k
  have hp := fact_pos k
  calc
    fact k < 2 * fact k := by omega
    _ <= (k + 1) * fact k := Nat.mul_le_mul_right (fact k) (by omega)

theorem factorialPair_ne (m : Nat) :
    factorialIterates D W (m + 2) ≠ factorialIterates D W (m + 3) := by
  intro h
  have hindex : fact (m + 2) = fact (m + 3) :=
    iterateAnswer_injective D W h
  have hstrict : fact (m + 2) < fact (m + 3) := by
    exact fact_succ_strict (by omega)
  omega

/-- At every finite budget there are distinct iterates that the whole stage
    cannot distinguish. -/
theorem every_stage_not_equality
    (W : OldFixingContextWitness D) (m : Nat) :
    exists x y : Free.GeneratedAns D,
      x ≠ y ∧ FiniteTagEqAt D m x y := by
  refine ⟨factorialIterates D W (m + 2),
    factorialIterates D W (m + 3), factorialPair_ne D W m, ?_⟩
  exact factorialIterates_eqAt D W (by omega) (by omega)

/-- The concrete witness pair at stage `m` has separation rank strictly
    greater than `m`.  Thus separation ranks are unbounded. -/
theorem factorialPair_separationRank_gt (m : Nat) :
    m < finiteSeparationRank D
      (factorialIterates D W (m + 2))
      (factorialIterates D W (m + 3)) := by
  apply (finiteTagEqAt_iff_lt_rank D (factorialPair_ne D W m) m).1
  exact factorialIterates_eqAt D W (by omega) (by omega)

/-! ## An explicit new completion point -/

def factorialIteratesCauchySeq :
    Filtered.CauchySeq (generatedFilteredSpace D) where
  term := factorialIterates D W
  cauchy := factorialIterates_cauchy D W

def completionWitness :
    Filtered.Completion (generatedFilteredSpace D) :=
  Filtered.classOf (generatedFilteredSpace D)
    (factorialIteratesCauchySeq D W)

theorem completionWitness_ne_embed (x : Free.GeneratedAns D) :
    completionWitness D W ≠ Filtered.embed (generatedFilteredSpace D) x := by
  intro h
  apply factorialIterates_noLimit D W x
  have hclass :
      Filtered.classOf (generatedFilteredSpace D)
          (factorialIteratesCauchySeq D W) =
        Filtered.embed (generatedFilteredSpace D) x := by
    simpa [completionWitness] using h
  have hconv :=
    (Filtered.classOf_eq_embed_iff
      (generatedFilteredSpace D) (factorialIteratesCauchySeq D W) x).1 hclass
  simpa [factorialIteratesCauchySeq] using hconv

/-- The canonical completion embedding is not surjective. -/
theorem completionEmbedding_not_surjective
    (W : OldFixingContextWitness D) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) := by
  intro hsurj
  rcases hsurj (completionWitness D W) with ⟨x, hx⟩
  exact completionWitness_ne_embed D W x hx.symm

/-- The completion contains an explicit point outside the generated image. -/
theorem completion_adds_point (W : OldFixingContextWitness D) :
    exists q : Filtered.Completion (generatedFilteredSpace D),
      forall x : Free.GeneratedAns D,
        Filtered.embed (generatedFilteredSpace D) x ≠ q := by
  refine ⟨completionWitness D W, ?_⟩
  intro x
  exact Ne.symm (completionWitness_ne_embed D W x)

end OldFixingContextProperness
end Resolution
