import ResolutionPigeonhole

/-!
# Orbits on a bounded state space are eventually periodic

The completion witness of `paper/COMPLETION-ADDS-POINTS.md` needs one fact
about an arbitrary stage-`n` observer: since it has only finitely many states,
iterating it from a fixed start must cycle, and the cycle length is bounded by
the number of states. Everything downstream is then arithmetic.

`Std` supplies no finiteness machinery, so a state space is presented here by an
explicit injective bound (`Coded`), which is all the argument uses and which the
concrete carrier `Unit ⊕ Fin n ⊕ Unit` satisfies by construction.

The payoff is `orbit_eq_of_factorial_dvd`: past index `N`, orbit values agree
whenever their indices differ by a multiple of `N !`. Factorial appears rather
than the sharper `lcm (1..N)` because it is the weaker fact and it suffices.
-/

universe u

namespace Resolution
namespace Orbit

/-! ## Factorial -/

/-- Factorial, absent from `Std`. -/
def fact : Nat -> Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : forall n : Nat, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem le_fact : forall n : Nat, n <= fact n
  | 0 => Nat.zero_le _
  | n + 1 => by
      have h := fact_pos n
      calc n + 1 = (n + 1) * 1 := by omega
        _ <= (n + 1) * fact n := Nat.mul_le_mul_left _ h
        _ = fact (n + 1) := rfl

/-- Every positive number at most `n` divides `n !`. -/
theorem dvd_fact : forall (n p : Nat), 0 < p -> p <= n -> p ∣ fact n
  | 0, p, hp, hpn => absurd hpn (by omega)
  | n + 1, p, hp, hpn => by
      by_cases hEq : p = n + 1
      · exact ⟨fact n, by rw [hEq]; rfl⟩
      · have hle : p <= n := by omega
        rcases dvd_fact n p hp hle with ⟨c, hc⟩
        exact ⟨(n + 1) * c, by rw [show fact (n+1) = (n+1) * fact n from rfl,
          hc, Nat.mul_left_comm]⟩

/-- `fact` is monotone under divisibility along `≤`. -/
theorem fact_dvd_fact : forall (n m : Nat), n <= m -> fact n ∣ fact m := by
  intro n m
  induction m with
  | zero =>
      intro h
      have : n = 0 := by omega
      subst this
      exact Nat.dvd_refl _
  | succ k ih =>
      intro h
      by_cases hEq : n = k + 1
      · subst hEq
        exact Nat.dvd_refl _
      · have hle : n <= k := by omega
        rcases ih hle with ⟨c, hc⟩
        exact ⟨(k + 1) * c, by
          rw [show fact (k+1) = (k+1) * fact k from rfl, hc,
            Nat.mul_left_comm]⟩

/-! ## Coded state spaces -/

/-- A state space presented by an injective bound. This replaces `Fintype`,
    which `Std` does not provide. -/
structure Coded (S : Type u) (N : Nat) where
  code : S -> Nat
  code_lt : forall s : S, code s < N
  code_inj : forall s t : S, code s = code t -> s = t

/-- The orbit of `s0` under iterated `g`. -/
def orb {S : Type u} (g : S -> S) (s0 : S) : Nat -> S
  | 0 => s0
  | k + 1 => g (orb g s0 k)

theorem orb_succ {S : Type u} (g : S -> S) (s0 : S) (k : Nat) :
    orb g s0 (k + 1) = g (orb g s0 k) := rfl

/-- Shifting an orbit is the orbit of the shifted start. -/
theorem orb_add {S : Type u} (g : S -> S) (s0 : S) :
    forall (a b : Nat), orb g s0 (a + b) = orb g (orb g s0 a) b
  | _, 0 => rfl
  | a, b + 1 => by
      show g (orb g s0 (a + b)) = g (orb g (orb g s0 a) b)
      rw [orb_add g s0 a b]

/-! ## Eventual periodicity -/

section

variable {S : Type u} {N : Nat} (g : S -> S) (s0 : S)

/-- Two orbit indices within the first `N + 1` collide. -/
theorem orb_repeat (C : Coded S N) :
    ∃ i j : Nat, i < j ∧ j <= N ∧ orb g s0 i = orb g s0 j := by
  have hb : forall i : Nat, i <= N -> C.code (orb g s0 i) < N := by
    intro i _
    exact C.code_lt _
  rcases Resolution.Pigeon.boundedRepeat N
      (fun i => C.code (orb g s0 i)) hb with ⟨i, j, hij, hjN, heq⟩
  exact ⟨i, j, hij, hjN, C.code_inj _ _ heq⟩

/-- Once the orbit repeats with period `p`, it repeats forever. -/
theorem orb_period_forward
    {t p : Nat} (h : orb g s0 (t + p) = orb g s0 t) :
    forall k : Nat, orb g s0 (t + k + p) = orb g s0 (t + k) := by
  intro k
  rw [show t + k + p = (t + p) + k from by omega,
    orb_add g s0 (t + p) k, h, orb_add g s0 t k]

/-- Any multiple of the period may be added past the tail. -/
theorem orb_period_multiple
    {t p : Nat} (h : orb g s0 (t + p) = orb g s0 t) :
    forall (k c : Nat), orb g s0 (t + k + c * p) = orb g s0 (t + k) := by
  intro k c
  induction c with
  | zero => rw [Nat.zero_mul, Nat.add_zero]
  | succ d ih =>
      have hstep : orb g s0 (t + (k + d * p) + p) = orb g s0 (t + (k + d * p)) :=
        orb_period_forward g s0 h (k + d * p)
      have hrw : t + k + (d + 1) * p = t + (k + d * p) + p := by
        have : (d + 1) * p = d * p + p := by
          simp [Nat.succ_mul]
        omega
      rw [hrw, hstep, show t + (k + d * p) = t + k + d * p from by omega, ih]

/-- **The fact the completion witness consumes.** Past index `N`, orbit values
    depend only on the index modulo `N !`. -/
theorem orbit_eq_of_factorial_dvd (C : Coded S N)
    {i j : Nat} (hi : N <= i) (hij : i <= j) (hdvd : fact N ∣ (j - i)) :
    orb g s0 i = orb g s0 j := by
  rcases orb_repeat g s0 C with ⟨a, b, hab, hbN, hEq⟩
  -- period `p = b - a`, tail starts at `a`
  have hp : 0 < b - a := by omega
  have hpN : b - a <= N := by omega
  have hper : orb g s0 (a + (b - a)) = orb g s0 a := by
    rw [show a + (b - a) = b from by omega]
    exact hEq.symm
  rcases hdvd with ⟨c, hc⟩
  rcases dvd_fact N (b - a) hp hpN with ⟨d, hd⟩
  have hai : a <= i := by omega
  have hkey := orb_period_multiple g s0 hper (i - a) (c * d)
  rw [show a + (i - a) = i from by omega] at hkey
  -- `hkey : orb g s0 (i + c * d * (b - a)) = orb g s0 i`
  have hmul : i + c * d * (b - a) = j := by
    have hstep : c * d * (b - a) = j - i := by
      rw [hc, hd]
      simp [Nat.mul_comm, Nat.mul_assoc]
    omega
  rw [hmul] at hkey
  exact hkey.symm

end

/-! ## The concrete observer carrier

A stage-`n` finite-tag model over a one-point old carrier has state space
`Unit ⊕ (Fin n ⊕ Unit)` — the old point, the `n` fresh tags, and overflow.
That is `n + 2` states, and the coding below is the bridge from the orbit
machinery to the Resolution side. It is stated for the bare type so this module
keeps its `Std`-only dependency. -/

/-- The state space of a stage-`n` observer over a one-point old carrier. -/
abbrev TagState (n : Nat) := Sum Unit (Sum (Fin n) Unit)

/-- Number the old point `0`, tag `i` as `i + 1`, and overflow last. -/
def tagCode {n : Nat} : TagState n -> Nat
  | .inl _ => 0
  | .inr (.inl i) => i.val + 1
  | .inr (.inr _) => n + 1

theorem tagCode_lt {n : Nat} : forall s : TagState n, tagCode s < n + 2
  | .inl _ => by show (0 : Nat) < n + 2; omega
  | .inr (.inl i) => by
      show i.val + 1 < n + 2
      have := i.isLt
      omega
  | .inr (.inr _) => by show n + 1 < n + 2; omega

theorem tagCode_inj {n : Nat} :
    forall s t : TagState n, tagCode s = tagCode t -> s = t
  | .inl _, .inl _, _ => rfl
  | .inl _, .inr (.inl j), h => by
      have := j.isLt; simp [tagCode] at h
  | .inl _, .inr (.inr _), h => by simp [tagCode] at h
  | .inr (.inl i), .inl _, h => by
      have := i.isLt; simp [tagCode] at h
  | .inr (.inl i), .inr (.inl j), h => by
      have hij : i.val = j.val := by simp [tagCode] at h; omega
      exact congrArg (fun v => Sum.inr (Sum.inl v)) (Fin.ext hij)
  | .inr (.inl i), .inr (.inr _), h => by
      have := i.isLt; simp [tagCode] at h; omega
  | .inr (.inr _), .inl _, h => by simp [tagCode] at h
  | .inr (.inr _), .inr (.inl j), h => by
      have := j.isLt; simp [tagCode] at h; omega
  | .inr (.inr _), .inr (.inr _), _ => rfl

/-- A stage-`n` observer over a one-point old carrier has `n + 2` states. -/
def tagCoded (n : Nat) : Coded (TagState n) (n + 2) where
  code := tagCode
  code_lt := tagCode_lt
  code_inj := tagCode_inj

end Orbit
end Resolution
