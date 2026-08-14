import ResolutionCompletionProbe
import ResolutionOrbit

/-!
# Properness of the finite-tag observational completion over a finite base

This module gives an exact structural criterion for the completion to be
proper when the old carrier is presented by a finite code.

* If the old algebra is total, every generated Answer is old.  A Cauchy
  sequence is therefore eventually constant, so the generated filtered space
  is complete.
* If one old application is undefined, the factorially indexed combs at that
  application are Cauchy whenever the old carrier is finite.  They do not
  converge to any generated Answer.  The nonconvergence argument uses a
  preserving finite-tag model selected from the candidate Answer and a finite
  comb prefix; after that prefix the overflow state is absorbing.

Thus, for a finitely coded old carrier, the canonical completion embedding is
surjective exactly when the old algebra is total.
-/

universe u v

namespace Resolution
namespace FiniteBaseProperness

open Resolution.External
open Resolution.Orbit
open Resolution.External.FiniteTagProof

variable {Sigma : Signature.{u}}

/-- Every old operation is defined. -/
def IsTotal (D : PartialAlg.{u,v} Sigma) : Prop :=
  forall (f : Sigma.Op) (a b : D.Carrier),
    exists c : D.Carrier, D.eval f a b = some c

/-! ## Finite coding of a finite-tag carrier -/

/-- Extend a finite code for the old carrier by consecutive codes for the
    fresh tags and one final code for overflow. -/
def finiteTagCode
    (D : PartialAlg.{u,v} Sigma) {baseSize n : Nat}
    (C : Coded D.Carrier baseSize) :
    FiniteTagCarrier D n -> Nat
  | Sum.inl a => C.code a
  | Sum.inr (Sum.inl i) => baseSize + i.val
  | Sum.inr (Sum.inr _) => baseSize + n

theorem finiteTagCode_lt
    (D : PartialAlg.{u,v} Sigma) {baseSize n : Nat}
    (C : Coded D.Carrier baseSize) :
    forall s : FiniteTagCarrier D n,
      finiteTagCode D C s < baseSize + n + 1
  | Sum.inl a => by
      change C.code a < baseSize + n + 1
      have ha := C.code_lt a
      omega
  | Sum.inr (Sum.inl i) => by
      change baseSize + i.val < baseSize + n + 1
      have hi := i.isLt
      omega
  | Sum.inr (Sum.inr _) => by
      change baseSize + n < baseSize + n + 1
      omega

theorem finiteTagCode_inj
    (D : PartialAlg.{u,v} Sigma) {baseSize n : Nat}
    (C : Coded D.Carrier baseSize) :
    forall s t : FiniteTagCarrier D n,
      finiteTagCode D C s = finiteTagCode D C t -> s = t
  | Sum.inl a, Sum.inl b, h => by
      exact congrArg (fun x =>
        (Sum.inl x : FiniteTagCarrier D n)) (C.code_inj a b h)
  | Sum.inl a, Sum.inr (Sum.inl j), h => by
      have ha := C.code_lt a
      have hj := j.isLt
      simp only [finiteTagCode] at h
      omega
  | Sum.inl a, Sum.inr (Sum.inr _), h => by
      have ha := C.code_lt a
      simp only [finiteTagCode] at h
      omega
  | Sum.inr (Sum.inl i), Sum.inl b, h => by
      have hi := i.isLt
      have hb := C.code_lt b
      simp only [finiteTagCode] at h
      omega
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j), h => by
      have hij : i.val = j.val := by
        simp only [finiteTagCode] at h
        omega
      exact congrArg (fun x =>
        (Sum.inr (Sum.inl x) : FiniteTagCarrier D n)) (Fin.ext hij)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr _), h => by
      have hi := i.isLt
      simp only [finiteTagCode] at h
      omega
  | Sum.inr (Sum.inr _), Sum.inl b, h => by
      have hb := C.code_lt b
      simp only [finiteTagCode] at h
      omega
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl j), h => by
      have hj := j.isLt
      simp only [finiteTagCode] at h
      omega
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inr _), _ => rfl

/-- A stage-`n` observer over a base coded by `baseSize` has at most
    `baseSize + n + 1` states. -/
def finiteTagCoded
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize) (n : Nat) :
    Coded (FiniteTagCarrier D n) (baseSize + n + 1) where
  code := finiteTagCode D C
  code_lt := finiteTagCode_lt D C
  code_inj := finiteTagCode_inj D C

/-! ## The Cauchy half: finite bases force factorial combs to stabilize -/

section UndefinedApplication

variable (D : PartialAlg.{u,v} Sigma)
variable (f : Sigma.Op) (a z : D.Carrier)

/-- The combs sampled at factorial indices. -/
noncomputable def factorialCombs (k : Nat) : Free.GeneratedAns D :=
  Resolution.Probe.comb D f a z (fact k)

def basePoint {n : Nat} : FiniteTagCarrier D n := Sum.inl a

/-- A fixed finite-tag observer acts on the comb family by iterating this map. -/
def observerStep {n : Nat} (T : FiniteTagAlg D n) :
    FiniteTagCarrier D n -> FiniteTagCarrier D n :=
  fun s => T.op f s (Sum.inl z)

theorem foldComb_eq_orbit {n : Nat}
    (hUndefined : D.eval f a z = none)
    (T : FiniteTagAlg D n) :
    forall k : Nat,
      Free.TotalAlg.foldRaw D (T.toTotalAlg D)
          (Resolution.Probe.combRaw D f a z k) =
        orb (observerStep D f z T) (basePoint D a) k
  | 0 => rfl
  | k + 1 => by
      rw [Resolution.Probe.combRaw_succ D f a z hUndefined k]
      change T.op f
          (Free.TotalAlg.foldRaw D (T.toTotalAlg D)
            (Resolution.Probe.combRaw D f a z k))
          (Sum.inl z) = _
      rw [foldComb_eq_orbit hUndefined T k]
      rfl

theorem comb_eqAt_of_factorial_dvd
    {baseSize n : Nat} (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none)
    {i j : Nat}
    (hi : baseSize + n + 1 <= i) (hij : i <= j)
    (hdvd : fact (baseSize + n + 1) ∣ (j - i)) :
    FiniteTagEqAt D n
      (Resolution.Probe.comb D f a z i)
      (Resolution.Probe.comb D f a z j) := by
  intro T
  show Free.TotalAlg.foldRaw D (T.toTotalAlg D)
      (Resolution.Probe.combRaw D f a z i) =
    Free.TotalAlg.foldRaw D (T.toTotalAlg D)
      (Resolution.Probe.combRaw D f a z j)
  rw [foldComb_eq_orbit D f a z hUndefined T i,
      foldComb_eq_orbit D f a z hUndefined T j]
  exact orbit_eq_of_factorial_dvd
    (observerStep D f z T) (basePoint D a)
    (finiteTagCoded D C n) hi hij hdvd

theorem dvd_sub_of_dvd_of_dvd {d i j : Nat}
    (hi : d ∣ i) (hj : d ∣ j) : d ∣ (j - i) := by
  rcases hi with ⟨p, hp⟩
  rcases hj with ⟨q, hq⟩
  exact ⟨q - p, by rw [hp, hq, Nat.mul_sub_left_distrib]⟩

theorem factorialCombs_eqAt
    {baseSize n : Nat} (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none)
    {i j : Nat}
    (hi : baseSize + n + 1 <= i)
    (hj : baseSize + n + 1 <= j) :
    FiniteTagEqAt D n
      (factorialCombs D f a z i)
      (factorialCombs D f a z j) := by
  have hdi : fact (baseSize + n + 1) ∣ fact i :=
    fact_dvd_fact _ _ hi
  have hdj : fact (baseSize + n + 1) ∣ fact j :=
    fact_dvd_fact _ _ hj
  have hbi : baseSize + n + 1 <= fact i :=
    Nat.le_trans hi (le_fact i)
  have hbj : baseSize + n + 1 <= fact j :=
    Nat.le_trans hj (le_fact j)
  rcases Nat.le_total (fact i) (fact j) with hle | hle
  · exact comb_eqAt_of_factorial_dvd D f a z C hUndefined hbi hle
      (dvd_sub_of_dvd_of_dvd hdi hdj)
  · exact finiteTagEqAt_symm D n
      (comb_eqAt_of_factorial_dvd D f a z C hUndefined hbj hle
        (dvd_sub_of_dvd_of_dvd hdj hdi))

/-- Finiteness of the old carrier is exactly what is needed for the orbit
    argument: every fixed-stage observer has a bounded state space. -/
theorem factorialCombs_cauchy
    {baseSize : Nat} (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    Filtered.Cauchy (generatedFilteredSpace D)
      (factorialCombs D f a z) := by
  intro n
  exact ⟨baseSize + n + 1, fun i j hi hj =>
    factorialCombs_eqAt D f a z C hUndefined hi hj⟩

/-! ## The nonconvergence half: preservation-compatible saturation -/

theorem nodeCount_pos :
    forall t : RawAns Sigma D.Carrier,
      0 < nodeCount D t
  | .old _ => Nat.zero_lt_one
  | .susp _ l r => by
      show 0 < 1 + (nodeCount D l + nodeCount D r)
      omega

theorem nodeCount_le_of_mem_subterms :
    forall {s t : RawAns Sigma D.Carrier},
      s ∈ subterms D t -> nodeCount D s <= nodeCount D t := by
  intro s t h
  induction t with
  | old b =>
      simp only [subterms, List.mem_singleton] at h
      cases h
      exact Nat.le_refl _
  | susp g l r ihl ihr =>
      simp only [subterms, List.mem_cons, List.mem_append] at h
      rcases h with hroot | hl | hr
      · cases hroot
        exact Nat.le_refl _
      · have hle := ihl hl
        simp only [nodeCount]
        omega
      · have hle := ihr hr
        simp only [nodeCount]
        omega

theorem encode_ne_overflow_of_mem
    {x y s : RawAns Sigma D.Carrier}
    (hs : s ∈ selected D x y) :
    encode D x y s ≠ overflow D := by
  classical
  cases s with
  | old b =>
      simp [encode, overflow]
  | susp g l r =>
      rw [encode_susp_of_mem D hs]
      simp [overflow]

/-- No selected transition has overflow as the encoding of a child. -/
theorem table_overflow_left
    (x y : RawAns Sigma D.Carrier) (g : Sigma.Op)
    (q : FiniteTagCarrier D (selected D x y).length) :
    table D x y g (overflow D) q = overflow D := by
  classical
  have hnone : ¬(Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected D x y ∧ MatchNode D x y g (overflow D) q s) := by
    rintro ⟨s, hs, hm⟩
    cases s with
    | old b =>
        simp [MatchNode] at hm
    | susp op l r =>
        have hlmem := (children_mem_selected D hs).1
        have hne := encode_ne_overflow_of_mem D hlmem
        have hm0 := hm
        simp only [MatchNode] at hm0
        have hm' : encode D x y l = overflow D := by
          exact hm0.2.1
        exact hne hm'
  simp only [table, dif_neg hnone]

theorem finiteOp_overflow_left
    (x y : RawAns Sigma D.Carrier) (g : Sigma.Op)
    (q : FiniteTagCarrier D (selected D x y).length) :
    finiteOp D x y g (overflow D) q = overflow D := by
  change table D x y g (overflow D) q = overflow D
  exact table_overflow_left D x y g q

theorem old_right_mem_comb_subterms
    (hUndefined : D.eval f a z = none) (k : Nat) :
    (.old z : RawAns Sigma D.Carrier) ∈
      subterms D (Resolution.Probe.combRaw D f a z (k + 1)) := by
  rw [Resolution.Probe.combRaw_succ D f a z hUndefined k]
  simp [subterms, self_mem_subterms]

/-- A comb one step longer than the chosen prefix cannot already occur in the
    finite closure of the candidate and that prefix. -/
theorem comb_after_candidate_prefix_not_selected
    (hUndefined : D.eval f a z = none)
    (x : RawAns Sigma D.Carrier) :
    Resolution.Probe.combRaw D f a z (nodeCount D x + 2) ∉
      selected D x
        (Resolution.Probe.combRaw D f a z (nodeCount D x + 1)) := by
  intro hmem
  simp only [selected, List.mem_append] at hmem
  rcases hmem with hx | hp
  · have hle := nodeCount_le_of_mem_subterms D hx
    have hcount := Resolution.Probe.combRaw_nodeCount
      D f a z hUndefined (nodeCount D x + 2)
    omega
  · have hle := nodeCount_le_of_mem_subterms D hp
    have hnext := Resolution.Probe.combRaw_nodeCount
      D f a z hUndefined (nodeCount D x + 2)
    have hpref := Resolution.Probe.combRaw_nodeCount
      D f a z hUndefined (nodeCount D x + 1)
    omega

/-- Immediately after the candidate-sized prefix, the conservative selected
    table deliberately misses and returns overflow. -/
theorem table_after_candidate_prefix
    (hUndefined : D.eval f a z = none)
    (x : RawAns Sigma D.Carrier) :
    table D x
        (Resolution.Probe.combRaw D f a z (nodeCount D x + 1)) f
        (encode D x
          (Resolution.Probe.combRaw D f a z (nodeCount D x + 1))
          (Resolution.Probe.combRaw D f a z (nodeCount D x + 1)))
        (encode D x
          (Resolution.Probe.combRaw D f a z (nodeCount D x + 1))
          (.old z)) =
      overflow D := by
  classical
  let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
  have hpRoot : p ∈ selected D x p := right_root_mem_selected D x p
  have hzSub : (.old z : RawAns Sigma D.Carrier) ∈ subterms D p := by
    exact old_right_mem_comb_subterms D f a z hUndefined (nodeCount D x)
  have hzSel : (.old z : RawAns Sigma D.Carrier) ∈ selected D x p := by
    simp [selected, hzSub]
  have hnext : Resolution.Probe.combRaw D f a z (nodeCount D x + 2) ∉
      selected D x p := by
    exact comb_after_candidate_prefix_not_selected D f a z hUndefined x
  have hnone : ¬(Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected D x p ∧
        MatchNode D x p f (encode D x p p) (encode D x p (.old z)) s) := by
    rintro ⟨s, hs, hm⟩
    cases s with
    | old b =>
        simp [MatchNode] at hm
    | susp g l r =>
        have hc := children_mem_selected D hs
        have hm0 := hm
        simp only [MatchNode] at hm0
        have hm' : g = f ∧ encode D x p l = encode D x p p ∧
            encode D x p r = encode D x p (.old z) := by
          exact hm0
        have hl : l = p := encode_injective_on D hc.1 hpRoot hm'.2.1
        have hr : r = .old z := encode_injective_on D hc.2 hzSel hm'.2.2
        have hsNext : RawAns.susp g l r =
            Resolution.Probe.combRaw D f a z (nodeCount D x + 2) := by
          rw [Resolution.Probe.combRaw_succ D f a z hUndefined
            (nodeCount D x + 1)]
          cases hm'.1
          cases hl
          cases hr
          rfl
        exact hnext (hsNext ▸ hs)
  change table D x p f (encode D x p p) (encode D x p (.old z)) =
    overflow D
  simp only [table, dif_neg hnone]

theorem finiteOp_after_candidate_prefix
    (hUndefined : D.eval f a z = none)
    (x : RawAns Sigma D.Carrier) :
    finiteOp D x
        (Resolution.Probe.combRaw D f a z (nodeCount D x + 1)) f
        (encode D x
          (Resolution.Probe.combRaw D f a z (nodeCount D x + 1))
          (Resolution.Probe.combRaw D f a z (nodeCount D x + 1)))
        (encode D x
          (Resolution.Probe.combRaw D f a z (nodeCount D x + 1))
          (.old z)) =
      overflow D := by
  let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
  have hpRoot : p ∈ selected D x p := right_root_mem_selected D x p
  have hpShape : p = .susp f
      (Resolution.Probe.combRaw D f a z (nodeCount D x)) (.old z) := by
    exact Resolution.Probe.combRaw_succ D f a z hUndefined
      (nodeCount D x)
  change finiteOp D x p f (encode D x p p) (encode D x p (.old z)) =
    overflow D
  cases hpCase : p with
  | old b =>
      rw [hpCase] at hpShape
      cases hpShape
  | susp g l r =>
      have hsRoot : RawAns.susp g l r ∈
          selected D x (RawAns.susp g l r) :=
        right_root_mem_selected D x (RawAns.susp g l r)
      have henc : encode D x (RawAns.susp g l r) (RawAns.susp g l r) =
          (Sum.inr (Sum.inl
            (tagIndex (RawAns.susp g l r)
              (selected D x (RawAns.susp g l r)) hsRoot)) :
              FiniteTagCarrier D
                (selected D x (RawAns.susp g l r)).length) :=
        encode_susp_of_mem D hsRoot
      rw [henc]
      change table D x (RawAns.susp g l r) f
          (Sum.inr (Sum.inl
            (tagIndex (RawAns.susp g l r)
              (selected D x (RawAns.susp g l r)) hsRoot)))
          (encode D x (RawAns.susp g l r) (.old z)) = overflow D
      have htable := table_after_candidate_prefix D f a z hUndefined x
      change table D x p f (encode D x p p) (encode D x p (.old z)) =
        overflow D at htable
      rw [hpCase] at htable
      rw [henc] at htable
      exact htable

/-- The candidate-tailored preserving observer evaluates the first
    candidate-sized comb prefix to its selected tag. -/
theorem fold_candidate_prefix_eq_encode
    (hUndefined : D.eval f a z = none)
    (x : RawAns Sigma D.Carrier) :
    let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
    Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D) p =
      encode D x p p := by
  let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
  have hpNormal : Normal D p := by
    exact res_normal D (Resolution.Probe.combExpr D f a z (nodeCount D x + 1))
  exact foldRaw_eq_encode D p (right_root_mem_selected D x p) hpNormal

/-- The next comb enters overflow. -/
theorem fold_candidate_next_eq_overflow
    (hUndefined : D.eval f a z = none)
    (x : RawAns Sigma D.Carrier) :
    let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
    Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
        (Resolution.Probe.combRaw D f a z (nodeCount D x + 2)) =
      overflow D := by
  let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
  rw [Resolution.Probe.combRaw_succ D f a z hUndefined
    (nodeCount D x + 1)]
  change finiteOp D x p f
      (Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D) p)
      (Sum.inl z) = overflow D
  rw [fold_candidate_prefix_eq_encode D f a z hUndefined x]
  simpa only [encode] using
    (finiteOp_after_candidate_prefix D f a z hUndefined x)

/-- Once overflow is reached, all longer combs remain there. -/
theorem fold_candidate_tail_eq_overflow
    (hUndefined : D.eval f a z = none)
    (x : RawAns Sigma D.Carrier) :
    let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
    forall d : Nat,
      Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
          (Resolution.Probe.combRaw D f a z
            (nodeCount D x + 2 + d)) =
        overflow D := by
  let p := Resolution.Probe.combRaw D f a z (nodeCount D x + 1)
  change forall d : Nat,
    Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
        (Resolution.Probe.combRaw D f a z (nodeCount D x + 2 + d)) =
      overflow D
  intro d
  induction d with
  | zero =>
      simpa using fold_candidate_next_eq_overflow D f a z hUndefined x
  | succ d ih =>
      have hindex : nodeCount D x + 2 + (d + 1) =
          (nodeCount D x + 2 + d) + 1 := by omega
      rw [hindex, Resolution.Probe.combRaw_succ D f a z hUndefined
        (nodeCount D x + 2 + d)]
      change finiteOp D x p f
          (Free.TotalAlg.foldRaw D ((separatingAlg D x p).toTotalAlg D)
            (Resolution.Probe.combRaw D f a z (nodeCount D x + 2 + d)))
          (Sum.inl z) = overflow D
      rw [ih]
      exact finiteOp_overflow_left D x p f (Sum.inl z)

/-- The factorial comb sequence has no generated limit.  Unlike the Cauchy
    half, this statement requires no finiteness assumption on the old carrier. -/
theorem factorialCombs_noLimit
    (hUndefined : D.eval f a z = none)
    (x : Free.GeneratedAns D) :
    ¬(Filtered.Converges (generatedFilteredSpace D)
      (factorialCombs D f a z) x) := by
  intro hconv
  let p := Resolution.Probe.combRaw D f a z (nodeCount D x.1 + 1)
  let stage := (selected D x.1 p).length
  rcases hconv stage with ⟨N, hN⟩
  let K := N + nodeCount D x.1 + 2
  have hNK : N <= K := by omega
  have hlarge : nodeCount D x.1 + 2 <= fact K := by
    have hKfact := le_fact K
    omega
  have hindex : nodeCount D x.1 + 2 +
      (fact K - (nodeCount D x.1 + 2)) = fact K := by
    omega
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
          (Resolution.Probe.combRaw D f a z (fact K)) = overflow D := by
    rw [← hindex]
    exact fold_candidate_tail_eq_overflow D f a z hUndefined x.1
      (fact K - (nodeCount D x.1 + 2))
  have hmodel := hN K hNK (separatingAlg D x.1 p)
  change Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 p).toTotalAlg D) x.1 =
    Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 p).toTotalAlg D)
      (Resolution.Probe.combRaw D f a z (fact K)) at hmodel
  rw [hxFold, htail] at hmodel
  exact (encode_ne_overflow_of_mem D hxMem) hmodel

/-- A finite old carrier plus one genuinely undefined old application forces
    the observational completion to add points. -/
theorem not_complete_of_coded_of_undefined
    {baseSize : Nat} (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    ¬(Filtered.Complete (generatedFilteredSpace D)) := by
  intro hComplete
  rcases hComplete (factorialCombs D f a z)
      (factorialCombs_cauchy D f a z C hUndefined) with ⟨x, hx⟩
  exact factorialCombs_noLimit D f a z hUndefined x hx

end UndefinedApplication

/-! ## The total case -/

theorem res_eq_old_of_total
    (D : PartialAlg.{u,v} Sigma) (hTotal : IsTotal D) :
    forall e : Expr Sigma D.Carrier,
      exists a : D.Carrier, Expr.res D e = .old a
  | .val a => ⟨a, rfl⟩
  | .app f l r => by
      rcases res_eq_old_of_total D hTotal l with ⟨a, ha⟩
      rcases res_eq_old_of_total D hTotal r with ⟨b, hb⟩
      rcases hTotal f a b with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simp [Expr.res, ha, hb, PartialAlg.liftOp, hc]

theorem generated_eq_old_of_total
    (D : PartialAlg.{u,v} Sigma) (hTotal : IsTotal D)
    (x : Free.GeneratedAns D) :
    exists a : D.Carrier, x.1 = .old a := by
  rcases x.2 with ⟨e, he⟩
  rcases res_eq_old_of_total D hTotal e with ⟨a, ha⟩
  exact ⟨a, he.symm.trans ha⟩

/-- At tag budget two, total-base generated Answers agree only when equal. -/
theorem eq_of_eqAt_two_of_total
    (D : PartialAlg.{u,v} Sigma) (hTotal : IsTotal D)
    {x y : Free.GeneratedAns D}
    (hEq : FiniteTagEqAt D 2 x y) : x = y := by
  classical
  apply Classical.byContradiction
  intro hxy
  rcases generated_eq_old_of_total D hTotal x with ⟨a, hx⟩
  rcases generated_eq_old_of_total D hTotal y with ⟨b, hy⟩
  rcases finiteTag_pair_separation_bounded D x y hxy with
    ⟨n, hn, T, hT⟩
  have hn2 : n = 2 := by
    simp [hx, hy, nodeCount] at hn
    omega
  cases hn2
  exact hT (hEq T)

/-- A total old algebra has no genuinely new finite Answers, so every Cauchy
    sequence is eventually constant and already converges in the generated
    space.  This direction does not require the old carrier to be finite. -/
theorem complete_of_total
    (D : PartialAlg.{u,v} Sigma) (hTotal : IsTotal D) :
    Filtered.Complete (generatedFilteredSpace D) := by
  intro s hs
  rcases hs 2 with ⟨N, hN⟩
  refine ⟨s N, ?_⟩
  intro n
  refine ⟨N, ?_⟩
  intro k hk
  have heq : s N = s k :=
    eq_of_eqAt_two_of_total D hTotal (hN N k (Nat.le_refl N) hk)
  rw [heq]
  exact (generatedFilteredSpace D).eqAt_refl n (s k)

theorem exists_undefined_of_not_total
    (D : PartialAlg.{u,v} Sigma) (hNotTotal : ¬(IsTotal D)) :
    exists f : Sigma.Op, exists a b : D.Carrier,
      D.eval f a b = none := by
  classical
  apply Classical.byContradiction
  intro hNone
  apply hNotTotal
  intro f a b
  cases h : D.eval f a b with
  | none =>
      exact False.elim (hNone ⟨f, a, b, h⟩)
  | some c =>
      exact ⟨c, rfl⟩

/-- Failure of totality is exactly the existence of an undefined old
    application. -/
theorem not_total_iff_exists_undefined
    (D : PartialAlg.{u,v} Sigma) :
    (¬ IsTotal D) ↔
      exists f : Sigma.Op, exists a b : D.Carrier,
        D.eval f a b = none := by
  constructor
  · exact exists_undefined_of_not_total D
  · rintro ⟨f, a, b, hUndefined⟩ hTotal
    rcases hTotal f a b with ⟨c, hDefined⟩
    rw [hUndefined] at hDefined
    cases hDefined

/-! ## Exact finite-base criterion -/

/-- For a finitely coded old carrier, observational completeness is equivalent
    to totality of the old operation table. -/
theorem complete_iff_total
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize) :
    Filtered.Complete (generatedFilteredSpace D) ↔ IsTotal D := by
  constructor
  · intro hComplete
    classical
    apply Classical.byContradiction
    intro hNotTotal
    rcases exists_undefined_of_not_total D hNotTotal with ⟨f, a, z, hUndefined⟩
    exact (not_complete_of_coded_of_undefined D f a z C hUndefined) hComplete
  · intro hTotal
    exact complete_of_total D hTotal

/-- Equivalently, the canonical map onto the completion is surjective exactly
    for total finite-base algebras. -/
theorem completionEmbedding_surjective_iff_total
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize) :
    Function.Surjective (Filtered.embed (generatedFilteredSpace D)) ↔
      IsTotal D := by
  exact (Filtered.complete_iff_embed_surjective
    (generatedFilteredSpace D)).symm.trans (complete_iff_total D C)

/-- The requested properness theorem: over a finite base, the completion is
    proper exactly when at least one old application is undefined. -/
theorem completionEmbedding_not_surjective_iff_not_total
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize) :
    (¬(Function.Surjective
      (Filtered.embed (generatedFilteredSpace D)))) ↔
      ¬(IsTotal D) := by
  exact not_congr (completionEmbedding_surjective_iff_total D C)

/-- Paper-facing form of the properness criterion: over a finite base, the
    completion is proper exactly when an old application is undefined. -/
theorem completionEmbedding_not_surjective_iff_exists_undefined
    (D : PartialAlg.{u,v} Sigma) {baseSize : Nat}
    (C : Coded D.Carrier baseSize) :
    (¬(Function.Surjective
      (Filtered.embed (generatedFilteredSpace D)))) ↔
      exists f : Sigma.Op, exists a b : D.Carrier,
        D.eval f a b = none := by
  exact (completionEmbedding_not_surjective_iff_not_total D C).trans
    (not_total_iff_exists_undefined D)

end FiniteBaseProperness
end Resolution
