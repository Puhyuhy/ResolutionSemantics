import Std

/-!
# A pigeonhole principle, built from nothing

The project imports only `Std`, which supplies neither `Fintype` nor `Finite`,
so the counting argument needed by the completion witness
(`paper/COMPLETION-ADDS-POINTS.md`) has to be built rather than cited.

The statement proved here is the one that argument actually consumes:

  `boundedRepeat` — a `Nat`-indexed sequence whose values all lie below `N`
  repeats within its first `N + 1` terms.

The proof is by induction on the bound, shifting indices past a removed value
rather than performing surgery on `Fin`, which keeps every arithmetic side
condition inside `omega`.
-/

namespace Resolution
namespace Pigeon

/-- Skip index `k`: `shift k i` is `i` below `k` and `i + 1` from `k` up.
    This is the order-preserving injection `Nat → Nat` missing `k`. -/
def shift (k i : Nat) : Nat :=
  if i < k then i else i + 1

theorem shift_ne (k i : Nat) : shift k i ≠ k := by
  unfold shift
  split <;> omega

theorem shift_lt_succ {k i n : Nat} (h : i ≤ n) : shift k i ≤ n + 1 := by
  unfold shift
  split <;> omega

theorem shift_strictMono {k i j : Nat} (h : i < j) : shift k i < shift k j := by
  unfold shift
  split <;> split <;> omega

/-- A sequence bounded by `n` repeats within its first `n + 1` terms. -/
theorem boundedRepeat :
    forall (n : Nat) (h : Nat -> Nat),
      (forall i : Nat, i <= n -> h i < n) ->
        ∃ i j : Nat, i < j ∧ j <= n ∧ h i = h j := by
  intro n
  induction n with
  | zero =>
      intro h hb
      exact absurd (hb 0 (Nat.le_refl 0)) (by omega)
  | succ m ih =>
      intro h hb
      -- Either two of the first `m + 2` indices carry the top value `m`, or at
      -- most one does and we may delete it.
      by_cases htwo :
          ∃ a b : Nat, a < b ∧ b <= m + 1 ∧ h a = m ∧ h b = m
      · rcases htwo with ⟨a, b, hab, hbm, ha, hbv⟩
        exact ⟨a, b, hab, hbm, by rw [ha, hbv]⟩
      · -- No two indices share the top value, so shift past the one that may.
        by_cases hone : ∃ k : Nat, k <= m + 1 ∧ h k = m
        · rcases hone with ⟨k, hkm, hk⟩
          have hunique : forall i : Nat, i <= m + 1 -> h i = m -> i = k := by
            intro i him hi
            by_cases hne : i = k
            · exact hne
            · exact absurd
                (show ∃ a b : Nat, a < b ∧ b <= m + 1 ∧ h a = m ∧ h b = m from
                  if hlt : i < k then ⟨i, k, hlt, hkm, hi, hk⟩
                  else ⟨k, i, by omega, him, hk, hi⟩)
                htwo
          have hbound : forall i : Nat, i <= m -> h (shift k i) < m := by
            intro i him
            have hle : shift k i <= m + 1 := shift_lt_succ him
            have hlt : h (shift k i) < m + 1 := hb _ hle
            have hne : h (shift k i) ≠ m := by
              intro heq
              exact shift_ne k i (hunique _ hle heq)
            omega
          rcases ih (fun i => h (shift k i)) hbound with ⟨i, j, hij, hjm, heq⟩
          exact ⟨shift k i, shift k j, shift_strictMono hij,
            shift_lt_succ hjm, heq⟩
        · -- The top value is never taken, so the whole range is below `m`.
          have hbound : forall i : Nat, i <= m -> h i < m := by
            intro i him
            have hlt : h i < m + 1 := hb i (by omega)
            have hne : h i ≠ m := fun heq => hone ⟨i, by omega, heq⟩
            omega
          rcases ih h hbound with ⟨i, j, hij, hjm, heq⟩
          exact ⟨i, j, hij, by omega, heq⟩

end Pigeon
end Resolution
