import ResolutionFiniteTagProof

/-!
# The observational and prefix-depth filtrations differ

This module settles, by an explicit kernel-checked witness, the question that
gates Paper I (`paper/README.md`): is the finite-tag observational completion
just the prefix-depth (infinite-tree) completion in different notation?

It is not. The witness is the *comb* sequence of iterated singular
applications
`comb 0 = a`, `comb (k+1) = f (comb k) z` with `eval f a z` undefined —
in the arithmetic instance, the iterated division `((a / 0) / 0) / 0 / ...`.

Two facts are proved about the same sequence:

* `comb_cauchy_depth` — the combs are Cauchy for prefix-depth agreement:
  `comb i` and `comb j` agree to depth `n` whenever `i, j ≥ n`. Under the
  standard tree metric the sequence converges to the infinite comb.

* `comb_not_cauchy_observational` — the combs are **not** Cauchy in the
  finite-tag filtration: a single preserving model with **one** fresh tag
  (`oneTagModel`) distinguishes `comb k` from `comb (k+1)` for every `k`,
  so the sequence never settles at observation stage 1.

What is *kernel-checked* here is exactly the two-uniformity statement: the
identity map on generated Answers does not carry depth-Cauchy sequences to
observationally Cauchy ones, so the two filtrations induce different
uniformities.

The consequence for the completions is a standard informal inference on top of
that, recorded here and not formalized: any uniformly continuous isomorphism
commuting with the two canonical embeddings would carry the depth-limit of the
combs to an observational limit of their images, forcing that image sequence to
be observationally Cauchy, which `comb_not_cauchy_observational` refutes. So the
paper's completion is not a re-derivation of the metric infinite-tree completion
(Arnold–Nivat, Courcelle); its finite observations see through unbounded depth
at a fixed budget.

In the concrete arithmetic instance the effect is sharper still:
`natComb_pairwise_separated_at_zero` separates **all** distinct combs with
**zero** fresh tags, using only the pinned old carrier (`natZeroTagModel`
sends every singular division to the successor of its numerator). Depth-equal
prefixes of any two distinct combs are told apart by a tag-free observer.

The bound direction is worth recording: `finiteSeparationBound` guarantees
separation of `comb k` and `comb (k+1)` within `4k + 4` tags; these models do
it with one, or zero. The linear budget is thus far from tight on deep pairs —
data for adversarial question 2 of `paper/INDEPENDENT_REVIEW_CHECKLIST.md`.

What this module deliberately does **not** claim: that the observational
completion adds any points (adversarial question 4). That question is opened,
not closed, by these results — the same fresh-value freedom that powers
`natZeroTagModel` suggests the arithmetic filtration may be very fine, and how
fine is the next investigation.
-/

universe u v

namespace Resolution
namespace Probe

variable {Sigma : Signature.{u}}

/-! ## The comb sequence -/

/-- Left comb of iterated applications: `combExpr (k+1) = f (combExpr k) z`. -/
def combExpr (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier) :
    Nat -> Expr Sigma D.Carrier
  | 0 => .val a
  | k + 1 => .app f (combExpr D f a z k) (.val z)

/-- The resolved raw Answer of the `k`-th comb expression. -/
def combRaw (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier)
    (k : Nat) : RawAns Sigma D.Carrier :=
  Expr.res D (combExpr D f a z k)

/-- The `k`-th comb as a generated Answer, with its witness expression. -/
def comb (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier)
    (k : Nat) : Free.GeneratedAns D :=
  ⟨combRaw D f a z k, ⟨combExpr D f a z k, rfl⟩⟩

@[simp] theorem comb_val
    (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier) (k : Nat) :
    (comb D f a z k).1 = combRaw D f a z k :=
  rfl

@[simp] theorem combRaw_zero
    (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier) :
    combRaw D f a z 0 = .old a :=
  rfl

section Undefined

variable (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier)

/-- When the base application is undefined, every comb step suspends. -/
theorem combRaw_succ (h : D.eval f a z = none) :
    forall k : Nat,
      combRaw D f a z (k + 1) = .susp f (combRaw D f a z k) (.old z)
  | 0 => by
      show D.liftOp f (.old a) (.old z) = _
      simp [PartialAlg.liftOp, h]
  | k + 1 => by
      show D.liftOp f (combRaw D f a z (k + 1)) (.old z) = _
      rw [combRaw_succ h k]
      rfl

/-- Comb Answers grow without bound: `nodeCount (combRaw k) = 2k + 1`. -/
theorem combRaw_nodeCount (h : D.eval f a z = none) :
    forall k : Nat,
      External.FiniteTagProof.nodeCount D (combRaw D f a z k) = 2 * k + 1
  | 0 => rfl
  | k + 1 => by
      rw [combRaw_succ D f a z h k]
      show 1 + (External.FiniteTagProof.nodeCount D (combRaw D f a z k)
        + External.FiniteTagProof.nodeCount D (.old z)) = _
      rw [combRaw_nodeCount h k]
      show 1 + (2 * k + 1 + 1) = 2 * (k + 1) + 1
      omega

end Undefined

/-! ## A one-tag observer that never loses count of the combs

The model's non-old states are the single tag `t` and the overflow `⋆`. Old
pairs evaluate when defined; an undefined old pair steps to `t`; from then on
the left operand alone drives a two-cycle `t → ⋆ → t`. Adjacent combs land on
different states forever, at tag budget 1. -/

/-- The single fresh tag of a 1-tag carrier. -/
def probeTag (D : PartialAlg.{u,v} Sigma) : External.FiniteTagCarrier D 1 :=
  Sum.inr (Sum.inl (0 : Fin 1))

/-- The overflow state of a 1-tag carrier. -/
def probeStar (D : PartialAlg.{u,v} Sigma) : External.FiniteTagCarrier D 1 :=
  Sum.inr (Sum.inr ())

/-- Operation table: defined old pairs are pinned; undefined old pairs step to
    the tag; the tag steps to overflow; overflow steps back to the tag. -/
def probeOp (D : PartialAlg.{u,v} Sigma) :
    Sigma.Op -> External.FiniteTagCarrier D 1 ->
      External.FiniteTagCarrier D 1 -> External.FiniteTagCarrier D 1
  | g, Sum.inl x, Sum.inl y =>
      match D.eval g x y with
      | some c => Sum.inl c
      | none => probeTag D
  | _, Sum.inr (Sum.inl _), _ => probeStar D
  | _, Sum.inr (Sum.inr _), _ => probeTag D
  | _, Sum.inl _, Sum.inr _ => probeStar D

/-- The one-tag comb observer is a preserving finite-tag algebra. -/
def oneTagModel (D : PartialAlg.{u,v} Sigma) : External.FiniteTagAlg D 1 where
  op := probeOp D
  preserve := by
    intro g x y c hc
    simp [probeOp, hc]

section Separation

variable (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier)

/-- The state sequence of the one-tag observer along the combs. -/
def probeState : Nat -> External.FiniteTagCarrier D 1
  | 0 => Sum.inl a
  | k + 1 => probeOp D f (probeState k) (Sum.inl z)

theorem foldRaw_comb (h : D.eval f a z = none) :
    forall k : Nat,
      Free.TotalAlg.foldRaw D ((oneTagModel D).toTotalAlg D)
          (combRaw D f a z k) =
        probeState D f a z k
  | 0 => rfl
  | k + 1 => by
      rw [combRaw_succ D f a z h k]
      show probeOp D f
          (Free.TotalAlg.foldRaw D ((oneTagModel D).toTotalAlg D)
            (combRaw D f a z k))
          (Sum.inl z) = _
      rw [foldRaw_comb h k]
      rfl

/-- From index 1 on, the observer alternates strictly between tag and
    overflow. -/
theorem probeState_flip (h : D.eval f a z = none) :
    forall k : Nat,
      (probeState D f a z (k + 1) = probeTag D ∧
        probeState D f a z (k + 2) = probeStar D) ∨
      (probeState D f a z (k + 1) = probeStar D ∧
        probeState D f a z (k + 2) = probeTag D)
  | 0 => by
      left
      constructor
      · show probeOp D f (Sum.inl a) (Sum.inl z) = probeTag D
        simp [probeOp, h]
      · show probeOp D f (probeState D f a z 1) (Sum.inl z) = probeStar D
        have h1 : probeState D f a z 1 = probeTag D := by
          show probeOp D f (Sum.inl a) (Sum.inl z) = probeTag D
          simp [probeOp, h]
        rw [h1]
        rfl
  | k + 1 => by
      rcases probeState_flip h k with ⟨_, h2⟩ | ⟨_, h2⟩
      · right
        refine ⟨h2, ?_⟩
        show probeOp D f (probeState D f a z (k + 2)) (Sum.inl z) = _
        rw [h2]
        rfl
      · left
        refine ⟨h2, ?_⟩
        show probeOp D f (probeState D f a z (k + 2)) (Sum.inl z) = _
        rw [h2]
        rfl

theorem probeState_adjacent_ne (h : D.eval f a z = none) (k : Nat) :
    probeState D f a z k ≠ probeState D f a z (k + 1) := by
  match k with
  | 0 =>
      have h1 : probeState D f a z 1 = probeTag D := by
        show probeOp D f (Sum.inl a) (Sum.inl z) = probeTag D
        simp [probeOp, h]
      rw [show probeState D f a z 0 = Sum.inl a from rfl, h1]
      simp [probeTag]
  | k' + 1 =>
      rcases probeState_flip D f a z h k' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rw [h1, h2] <;> simp [probeTag, probeStar]

/-- **Fixed-budget deep separation.** One preserving model with a single
    fresh tag distinguishes every pair of adjacent combs, at every depth. -/
theorem comb_separatesAt_one (h : D.eval f a z = none) (k : Nat) :
    External.FiniteTagSeparatesAt D
      (comb D f a z k) (comb D f a z (k + 1)) 1 := by
  refine ⟨oneTagModel D, ?_⟩
  show Free.TotalAlg.foldRaw D ((oneTagModel D).toTotalAlg D)
      (combRaw D f a z k) ≠
    Free.TotalAlg.foldRaw D ((oneTagModel D).toTotalAlg D)
      (combRaw D f a z (k + 1))
  rw [foldRaw_comb D f a z h k, foldRaw_comb D f a z h (k + 1)]
  exact probeState_adjacent_ne D f a z h k

end Separation

/-! ## The prefix-depth filtration -/

namespace Depth

variable {A : Type v}

/-- Agreement of two raw Answers on all levels strictly above depth `n`. -/
def agreeUpTo : Nat -> RawAns Sigma A -> RawAns Sigma A -> Prop
  | 0, _, _ => True
  | _ + 1, .old x, .old y => x = y
  | _ + 1, .old _, .susp _ _ _ => False
  | _ + 1, .susp _ _ _, .old _ => False
  | n + 1, .susp g l r, .susp g' l' r' =>
      g = g' ∧ agreeUpTo n l l' ∧ agreeUpTo n r r'

theorem agreeUpTo_refl : forall (n : Nat) (t : RawAns Sigma A), agreeUpTo n t t
  | 0, _ => trivial
  | _ + 1, .old _ => rfl
  | n + 1, .susp _ l r => ⟨rfl, agreeUpTo_refl n l, agreeUpTo_refl n r⟩

theorem agreeUpTo_symm :
    forall (n : Nat) (x y : RawAns Sigma A),
      agreeUpTo n x y -> agreeUpTo n y x
  | 0, _, _, _ => trivial
  | _ + 1, .old _, .old _, h => h.symm
  | _ + 1, .old _, .susp _ _ _, h => h.elim
  | _ + 1, .susp _ _ _, .old _, h => h.elim
  | n + 1, .susp _ l r, .susp _ l' r', ⟨hg, hl, hr⟩ =>
      ⟨hg.symm, agreeUpTo_symm n l l' hl, agreeUpTo_symm n r r' hr⟩

theorem agreeUpTo_trans :
    forall (n : Nat) (x y z : RawAns Sigma A),
      agreeUpTo n x y -> agreeUpTo n y z -> agreeUpTo n x z
  | 0, _, _, _, _, _ => trivial
  | _ + 1, .old _, .old _, .old _, hxy, hyz => hxy.trans hyz
  | _ + 1, .old _, .old _, .susp _ _ _, _, hyz => hyz.elim
  | _ + 1, .old _, .susp _ _ _, _, hxy, _ => hxy.elim
  | _ + 1, .susp _ _ _, .old _, _, hxy, _ => hxy.elim
  | _ + 1, .susp _ _ _, .susp _ _ _, .old _, _, hyz => hyz.elim
  | n + 1, .susp _ l r, .susp _ l' r', .susp _ l'' r'',
      ⟨hg, hl, hr⟩, ⟨hg', hl', hr'⟩ =>
      ⟨hg.trans hg',
        agreeUpTo_trans n l l' l'' hl hl',
        agreeUpTo_trans n r r' r'' hr hr'⟩

theorem agreeUpTo_antitone :
    forall (n m : Nat), n ≤ m ->
      forall (x y : RawAns Sigma A), agreeUpTo m x y -> agreeUpTo n x y
  | 0, _, _, _, _, _ => trivial
  | n + 1, 0, hnm, _, _, _ => absurd hnm (by omega)
  | _ + 1, _ + 1, _, .old _, .old _, h => h
  | _ + 1, _ + 1, _, .old _, .susp _ _ _, h => h.elim
  | _ + 1, _ + 1, _, .susp _ _ _, .old _, h => h.elim
  | n + 1, m + 1, hnm, .susp _ l r, .susp _ l' r', ⟨hg, hl, hr⟩ =>
      ⟨hg,
        agreeUpTo_antitone n m (by omega) l l' hl,
        agreeUpTo_antitone n m (by omega) r r' hr⟩

theorem agreeUpTo_all_eq :
    forall (x y : RawAns Sigma A),
      (forall n : Nat, agreeUpTo n x y) -> x = y
  | .old _, .old _, h => congrArg RawAns.old (h 1)
  | .old _, .susp _ _ _, h => (h 1).elim
  | .susp _ _ _, .old _, h => (h 1).elim
  | .susp _ l r, .susp _ l' r', h => by
      have hg : _ = _ := (h 1).1
      have hl : l = l' :=
        agreeUpTo_all_eq l l' (fun n => (h (n + 1)).2.1)
      have hr : r = r' :=
        agreeUpTo_all_eq r r' (fun n => (h (n + 1)).2.2)
      subst hg hl hr
      rfl

end Depth

/-- Generated Answers filtered by prefix-depth agreement. This is the
    filtration whose completion is the classical infinite-tree space. -/
def depthSpace (D : PartialAlg.{u,v} Sigma) : Filtered.Space.{max u v} where
  Carrier := Free.GeneratedAns D
  eqAt n x y := Depth.agreeUpTo n x.1 y.1
  eqAt_refl n x := Depth.agreeUpTo_refl n x.1
  eqAt_symm := by
    intro n x y h
    exact Depth.agreeUpTo_symm n _ _ h
  eqAt_trans := by
    intro n x y z hxy hyz
    exact Depth.agreeUpTo_trans n _ _ _ hxy hyz
  eqAt_antitone := by
    intro n m hnm x y h
    exact Depth.agreeUpTo_antitone n m hnm _ _ h
  separated := by
    intro x y hall
    exact Subtype.ext (Depth.agreeUpTo_all_eq _ _ hall)

section Contrast

variable (D : PartialAlg.{u,v} Sigma) (f : Sigma.Op) (a z : D.Carrier)

theorem comb_agreeUpTo (h : D.eval f a z = none) :
    forall (n i j : Nat), n ≤ i -> n ≤ j ->
      Depth.agreeUpTo n (combRaw D f a z i) (combRaw D f a z j)
  | 0, _, _, _, _ => trivial
  | n + 1, i, j, hi, hj => by
      match i, j with
      | i' + 1, j' + 1 =>
        rw [combRaw_succ D f a z h i', combRaw_succ D f a z h j']
        exact ⟨rfl,
          comb_agreeUpTo h n i' j' (by omega) (by omega),
          Depth.agreeUpTo_refl n (.old z)⟩

/-- The combs are Cauchy for prefix depth: they converge to the infinite comb
    in the classical tree completion. -/
theorem comb_cauchy_depth (h : D.eval f a z = none) :
    Filtered.Cauchy (depthSpace D) (comb D f a z) := by
  intro n
  exact ⟨n, fun i j hi hj => comb_agreeUpTo D f a z h n i j hi hj⟩

/-- The combs are **not** Cauchy for finite-tag observation: stage 1 already
    separates every adjacent pair. -/
theorem comb_not_cauchy_observational (h : D.eval f a z = none) :
    ¬ Filtered.Cauchy (External.generatedFilteredSpace D) (comb D f a z) := by
  intro hc
  rcases hc 1 with ⟨N, hN⟩
  have hEq : External.FiniteTagEqAt D 1
      (comb D f a z N) (comb D f a z (N + 1)) :=
    hN N (N + 1) (Nat.le_refl N) (by omega)
  rcases comb_separatesAt_one D f a z h N with ⟨T, hT⟩
  exact hT (hEq T)

/-- **Filtration contrast.** Any partial algebra with one undefined application
    carries a sequence that is Cauchy for prefix depth but observationally
    divergent. This proves that the two induced uniformities differ; it does
    not assert a refinement relation between them. -/
theorem depthCauchy_not_observationalCauchy (h : D.eval f a z = none) :
    ∃ s : Nat -> Free.GeneratedAns D,
      Filtered.Cauchy (depthSpace D) s ∧
      ¬ Filtered.Cauchy (External.generatedFilteredSpace D) s :=
  ⟨comb D f a z, comb_cauchy_depth D f a z h,
    comb_not_cauchy_observational D f a z h⟩

end Contrast

/-! ## The arithmetic instance: zero tags suffice

For natural-number arithmetic the old carrier is infinite, and a preserving
model may send singular divisions to *fresh old values*. Sending `x / 0` to
`x + 1` makes the observer count the comb's depth in the old carrier itself:
all distinct combs are separated with an empty tag alphabet. -/

namespace NatProbe

open External NatArithmetic

/-- Tag-free operation table: defined old pairs are pinned; a singular
    division steps to the successor of its numerator; junk overflows. -/
def natOp : Op -> FiniteTagCarrier alg 0 -> FiniteTagCarrier alg 0 ->
    FiniteTagCarrier alg 0
  | g, Sum.inl x, Sum.inl y =>
      match NatArithmetic.eval g x y with
      | some c => Sum.inl c
      | none => Sum.inl (x + 1)
  | _, _, _ => Sum.inr (Sum.inr ())

/-- The tag-free comb observer is a preserving finite-tag algebra. -/
def natZeroTagModel : FiniteTagAlg alg 0 where
  op := natOp
  preserve := by
    intro g x y c hc
    have hc' : NatArithmetic.eval g x y = some c := hc
    simp [natOp, hc']

/-- The iterated singular division `((a / 0) / 0) / ... / 0`, `k` times. -/
noncomputable def natComb (a : Nat) (k : Nat) : Answer :=
  comb alg Op.div a 0 k

theorem natComb_fold (a : Nat) :
    forall k : Nat,
      Free.TotalAlg.foldRaw alg (natZeroTagModel.toTotalAlg alg)
          (combRaw alg Op.div a 0 k) =
        Sum.inl (a + k)
  | 0 => rfl
  | k + 1 => by
      rw [combRaw_succ alg Op.div a 0 (eval_div_zero a) k]
      show natOp Op.div
          (Free.TotalAlg.foldRaw alg (natZeroTagModel.toTotalAlg alg)
            (combRaw alg Op.div a 0 k))
          (Sum.inl 0) = _
      rw [natComb_fold a k]
      show (match NatArithmetic.eval Op.div (a + k) 0 with
        | some c => (Sum.inl c : FiniteTagCarrier alg 0)
        | none => Sum.inl (a + k + 1)) = Sum.inl (a + (k + 1))
      rw [eval_div_zero (a + k)]
      rfl

/-- **Zero-tag deep separation in the paper's own example.** All distinct
    iterated singular divisions are distinguished by one preserving model
    with an empty tag alphabet. -/
theorem natComb_pairwise_separated_at_zero (a : Nat) {i j : Nat}
    (hij : i ≠ j) :
    FiniteTagSeparatesAt alg (natComb a i) (natComb a j) 0 := by
  refine ⟨natZeroTagModel, ?_⟩
  show Free.TotalAlg.foldRaw alg (natZeroTagModel.toTotalAlg alg)
      (combRaw alg Op.div a 0 i) ≠
    Free.TotalAlg.foldRaw alg (natZeroTagModel.toTotalAlg alg)
      (combRaw alg Op.div a 0 j)
  rw [natComb_fold a i, natComb_fold a j]
  intro hcontra
  have hsum : a + i = a + j := Sum.inl.inj hcontra
  exact hij (by omega)

/-- In the arithmetic instance the combs already diverge at observation
    stage zero, though they are depth-Cauchy. -/
theorem natComb_not_cauchy_at_zero (a : Nat) :
    ¬ Filtered.Cauchy (generatedFilteredSpace alg) (natComb a) := by
  intro hc
  rcases hc 0 with ⟨N, hN⟩
  have hEq : FiniteTagEqAt alg 0 (natComb a N) (natComb a (N + 1)) :=
    hN N (N + 1) (Nat.le_refl N) (by omega)
  rcases natComb_pairwise_separated_at_zero a
      (by omega : N ≠ N + 1) with ⟨T, hT⟩
  exact hT (hEq T)

theorem natComb_cauchy_depth (a : Nat) :
    Filtered.Cauchy (depthSpace alg) (natComb a) :=
  comb_cauchy_depth alg Op.div a 0 (eval_div_zero a)

end NatProbe

end Probe
end Resolution
