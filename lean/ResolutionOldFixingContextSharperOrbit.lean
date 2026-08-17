import ResolutionOldFixingContextProperness

/-!
# Sharper old-fixing orbit compression

The original proof collapses the entire base to one additional finite state,
which gives an `(n+2)!` synchronization bound at stage `n`.  For an old-fixing
context that extra state is unnecessary: if the orbit ever enters the base it
is already constant, while an orbit that has not entered the base lives in the
`n` tags plus overflow, hence in only `n+1` moving states.
-/

universe u v

namespace Resolution
namespace OldFixingContextProperness

open Resolution.External
open Resolution.Orbit

variable {Sigma : Signature.{u}}
variable (D : PartialAlg.{u,v} Sigma)
variable (W : OldFixingContextWitness D)
variable {n : Nat}

/-- Code the genuine complement `Fin n ⊕ Unit` into `Nat < n+1`. -/
def outsideCode : Sum (Fin n) Unit -> Nat
  | Sum.inl i => i.val
  | Sum.inr _ => n

theorem outsideCode_lt : forall q : Sum (Fin n) Unit, outsideCode q < n + 1
  | Sum.inl i => by
      have := i.isLt
      simp [outsideCode]
      omega
  | Sum.inr _ => by
      simp [outsideCode]

theorem outsideCode_inj :
    forall q r : Sum (Fin n) Unit, outsideCode q = outsideCode r -> q = r
  | Sum.inl i, Sum.inl j, h => by
      have hij : i.val = j.val := by simpa [outsideCode] using h
      exact congrArg Sum.inl (Fin.ext hij)
  | Sum.inl i, Sum.inr _, h => by
      have hi := i.isLt
      simp [outsideCode] at h
      omega
  | Sum.inr _, Sum.inl j, h => by
      have hj := j.isLt
      simp [outsideCode] at h
      omega
  | Sum.inr _, Sum.inr _, _ => rfl

/-- Before stage `n+1`, either the orbit has entered the pointwise-fixed base,
or two external orbit states have already repeated. -/
theorem observerOrbit_old_or_external_repeat
    (T : FiniteTagAlg D n) (s : FiniteTagCarrier D n) :
    (exists k : Nat, k <= n + 1 ∧ exists a : D.Carrier,
      orb (observerStep D W T) s k = Sum.inl a) ∨
    (exists i j : Nat, i < j ∧ j <= n + 1 ∧
      orb (observerStep D W T) s i = orb (observerStep D W T) s j) := by
  classical
  by_cases hOld : exists k : Nat, k <= n + 1 ∧ exists a : D.Carrier,
      orb (observerStep D W T) s k = Sum.inl a
  · exact Or.inl hOld
  · right
    have hOutside : forall k : Nat, k <= n + 1 ->
        exists q : Sum (Fin n) Unit,
          orb (observerStep D W T) s k = Sum.inr q := by
      intro k hk
      cases h : orb (observerStep D W T) s k with
      | inl a =>
          exfalso
          apply hOld
          exact ⟨k, hk, a, h⟩
      | inr q => exact ⟨q, h⟩
    let code : Nat -> Nat := fun k =>
      match hq : orb (observerStep D W T) s k with
      | Sum.inl _ => 0
      | Sum.inr q => outsideCode q
    have hBound : forall k : Nat, k <= n + 1 -> code k < n + 1 := by
      intro k hk
      rcases hOutside k hk with ⟨q, hq⟩
      simp [code, hq, outsideCode_lt]
    rcases Resolution.Pigeon.boundedRepeat (n + 1) code hBound with
      ⟨i, j, hij, hj, hcode⟩
    rcases hOutside i (by omega) with ⟨qi, hqi⟩
    rcases hOutside j hj with ⟨qj, hqj⟩
    have hc : outsideCode qi = outsideCode qj := by
      simpa [code, hqi, hqj] using hcode
    have hq : qi = qj := outsideCode_inj qi qj hc
    exact ⟨i, j, hij, hj, by simpa [hqi, hqj, hq]⟩

/-- Sharper synchronization: past `n+1`, a difference divisible by `(n+1)!`
is enough for equality in every stage-`n` old-fixing observer. -/
theorem observerOrbit_eq_of_sharper_factorial_dvd
    (T : FiniteTagAlg D n) (s : FiniteTagCarrier D n)
    {i j : Nat} (hi : n + 1 <= i) (hij : i <= j)
    (hdvd : fact (n + 1) ∣ (j - i)) :
    orb (observerStep D W T) s i = orb (observerStep D W T) s j := by
  rcases observerOrbit_old_or_external_repeat D W T s with hOld | hRep
  · rcases hOld with ⟨k, hk, a, hka⟩
    have hki : k <= i := by omega
    have hkj : k <= j := Nat.le_trans hki hij
    have hiForm : i = k + (i - k) := by omega
    have hjForm : j = k + (j - k) := by omega
    have hoi : orb (observerStep D W T) s i = Sum.inl a := by
      rw [hiForm, orb_add, hka, observerOrbit_old D W T]
    have hoj : orb (observerStep D W T) s j = Sum.inl a := by
      rw [hjForm, orb_add, hka, observerOrbit_old D W T]
    rw [hoi, hoj]
  · rcases hRep with ⟨a, b, hab, hb, hEq⟩
    have hp : 0 < b - a := by omega
    have hpN : b - a <= n + 1 := by omega
    have hper :
        orb (observerStep D W T) s (a + (b - a)) =
          orb (observerStep D W T) s a := by
      rw [show a + (b - a) = b from by omega]
      exact hEq.symm
    rcases hdvd with ⟨c, hc⟩
    rcases dvd_fact (n + 1) (b - a) hp hpN with ⟨d, hd⟩
    have hai : a <= i := by omega
    have hkey := orb_period_multiple (observerStep D W T) s hper
      (i - a) (c * d)
    rw [show a + (i - a) = i from by omega] at hkey
    have hmul : i + c * d * (b - a) = j := by
      have hstep : c * d * (b - a) = j - i := by
        rw [hc, hd]
        simp [Nat.mul_comm, Nat.mul_assoc]
      omega
    rw [hmul] at hkey
    exact hkey.symm

/-- The sharper orbit theorem transported to stage equivalence of generated
Answers. -/
theorem iterate_eqAt_of_sharper_factorial_dvd
    {i j : Nat} (hi : n + 1 <= i) (hij : i <= j)
    (hdvd : fact (n + 1) ∣ (j - i)) :
    FiniteTagEqAt D n (iterateAnswer D W i) (iterateAnswer D W j) := by
  intro T
  show Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W i) =
    Free.TotalAlg.foldRaw D (T.toTotalAlg D) (iterateRaw D W j)
  rw [fold_iterate_eq_orbit D W T i, fold_iterate_eq_orbit D W T j]
  exact observerOrbit_eq_of_sharper_factorial_dvd D W T _ hi hij hdvd

/-- In particular, the consecutive factorial pair `(n+1)!`, `(n+2)!` agrees
at stage `n`. -/
theorem sharper_factorial_pair_eqAt :
    FiniteTagEqAt D n
      (iterateAnswer D W (fact (n + 1)))
      (iterateAnswer D W (fact (n + 2))) := by
  have hi : n + 1 <= fact (n + 1) := le_fact (n + 1)
  have hij : fact (n + 1) <= fact (n + 2) := by
    exact Nat.le_of_dvd (fact_pos (n + 2))
      (fact_dvd_fact (n + 1) (n + 2) (by omega))
  apply iterate_eqAt_of_sharper_factorial_dvd D W hi hij
  rw [show fact (n + 2) = (n + 2) * fact (n + 1) from rfl]
  refine ⟨n + 1, ?_⟩
  omega

end OldFixingContextProperness
end Resolution
