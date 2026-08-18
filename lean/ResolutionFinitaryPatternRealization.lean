import Std

/-!
# Finite-pattern realization for arbitrary finitary signatures

This module is an independent generality probe.  The main Resolution kernel is
binary; here operation symbols carry an arbitrary finite arity.  We prove the
structural core of finite-pattern realization for any finite child-closed list
of normalized raw Answers.

The point is not to replace the binary kernel, but to test whether the
finite-tag + overflow construction has any genuinely binary dependency.
-/

universe u v

namespace Resolution
namespace FinitaryPattern

structure Signature where
  Op : Type u
  arity : Op -> Nat

structure PartialAlg (Sigma : Signature.{u}) where
  Carrier : Type v
  eval : forall f : Sigma.Op,
    (Fin (Sigma.arity f) -> Carrier) -> Option Carrier

inductive RawAns (Sigma : Signature.{u}) (A : Type v) where
  | old : A -> RawAns Sigma A
  | susp (f : Sigma.Op)
      (args : Fin (Sigma.arity f) -> RawAns Sigma A) : RawAns Sigma A

variable {Sigma : Signature.{u}}

namespace PartialAlg

variable (D : PartialAlg.{u,v} Sigma)

/-- A raw Answer is normalized when all children are normalized and a
suspended application on old children is genuinely undefined in the base. -/
def Normal : RawAns Sigma D.Carrier -> Prop
  | .old _ => True
  | .susp f args =>
      (forall i, Normal (args i)) ∧
      forall oldArgs : Fin (Sigma.arity f) -> D.Carrier,
        (forall i, args i = .old (oldArgs i)) ->
          D.eval f oldArgs = none

end PartialAlg

abbrev FiniteTagCarrier
    (D : PartialAlg.{u,v} Sigma) (n : Nat) : Type v :=
  D.Carrier ⊕ (Fin n ⊕ Unit)

structure FiniteTagAlg
    (D : PartialAlg.{u,v} Sigma) (n : Nat) where
  op : forall f : Sigma.Op,
    (Fin (Sigma.arity f) -> FiniteTagCarrier D n) ->
      FiniteTagCarrier D n
  preserve : forall (f : Sigma.Op)
      (args : Fin (Sigma.arity f) -> D.Carrier)
      (c : D.Carrier),
    D.eval f args = some c ->
      op f (fun i => (Sum.inl (args i) : FiniteTagCarrier D n)) =
        (Sum.inl c : FiniteTagCarrier D n)

namespace FiniteTagAlg

variable {D : PartialAlg.{u,v} Sigma} {n : Nat}

/-- Interpretation of raw Answers in a finite-tag observer. -/
def foldRaw (T : FiniteTagAlg D n) :
    RawAns Sigma D.Carrier -> FiniteTagCarrier D n
  | .old a => Sum.inl a
  | .susp f args => T.op f (fun i => foldRaw T (args i))

end FiniteTagAlg

namespace Proof

variable (D : PartialAlg.{u,v} Sigma)

/-- First-occurrence index in a finite selected list. -/
def locate [DecidableEq A] (a : A) :
    (xs : List A) -> a ∈ xs -> Fin xs.length
  | [], h => False.elim (by simpa using h)
  | b :: bs, h =>
      if hab : a = b then
        ⟨0, Nat.succ_pos _⟩
      else
        let htail : a ∈ bs := by
          simpa [List.mem_cons, hab] using h
        let p := locate a bs htail
        ⟨p.val + 1, Nat.succ_lt_succ p.isLt⟩

@[simp] theorem get_locate [DecidableEq A] (a : A) :
    forall (xs : List A) (h : a ∈ xs), xs.get (locate a xs h) = a := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp at h
  | cons b bs ih =>
      intro h
      by_cases hab : a = b
      · subst b
        simp [locate]
      · have htail : a ∈ bs := by
          simpa [List.mem_cons, hab] using h
        simpa [locate, hab, htail] using ih htail

theorem locate_injective_on [DecidableEq A]
    {a b : A} {xs : List A} (ha : a ∈ xs) (hb : b ∈ xs)
    (h : locate a xs ha = locate b xs hb) : a = b := by
  calc
    a = xs.get (locate a xs ha) := (get_locate a xs ha).symm
    _ = xs.get (locate b xs hb) := congrArg xs.get h
    _ = b := get_locate b xs hb

noncomputable def tagIndex (a : A) (xs : List A) (h : a ∈ xs) :
    Fin xs.length := by
  classical
  exact locate a xs h

theorem tagIndex_injective_on {a b : A} {xs : List A}
    (ha : a ∈ xs) (hb : b ∈ xs)
    (h : tagIndex a xs ha = tagIndex b xs hb) : a = b := by
  classical
  apply locate_injective_on ha hb
  simpa [tagIndex] using h

/-- Overflow for all transitions not prescribed by the finite pattern. -/
def overflow {selected : List (RawAns Sigma D.Carrier)} :
    FiniteTagCarrier D selected.length :=
  Sum.inr (Sum.inr ())

/-- Old leaves retain their base value; selected suspensions receive a finite
tag; everything else is sent to overflow. -/
noncomputable def encode
    (selected : List (RawAns Sigma D.Carrier)) :
    RawAns Sigma D.Carrier -> FiniteTagCarrier D selected.length
  | .old a => Sum.inl a
  | t@(.susp _ _) => by
      classical
      exact if h : t ∈ selected then
        Sum.inr (Sum.inl (tagIndex t selected h))
      else overflow D

@[simp] theorem encode_susp_of_mem
    {selected : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op}
    {args : Fin (Sigma.arity f) -> RawAns Sigma D.Carrier}
    (h : RawAns.susp f args ∈ selected) :
    encode D selected (RawAns.susp f args) =
      (Sum.inr (Sum.inl (tagIndex (RawAns.susp f args) selected h)) :
        FiniteTagCarrier D selected.length) := by
  classical
  simp only [encode, dif_pos h]

/-- Encoding is injective on the selected finite pattern. -/
theorem encode_injective_on
    {selected : List (RawAns Sigma D.Carrier)}
    {s t : RawAns Sigma D.Carrier}
    (hs : s ∈ selected) (ht : t ∈ selected)
    (henc : encode D selected s = encode D selected t) : s = t := by
  classical
  cases s with
  | old a =>
      cases t with
      | old b =>
          simp only [encode] at henc
          exact congrArg RawAns.old (Sum.inl.inj henc)
      | susp g args =>
          simp [encode, ht] at henc
  | susp f args =>
      cases t with
      | old b =>
          simp [encode, hs] at henc
      | susp g args' =>
          have henc' := henc
          rw [encode_susp_of_mem D hs, encode_susp_of_mem D ht] at henc'
          have hidx :
              tagIndex (RawAns.susp f args) selected hs =
                tagIndex (RawAns.susp g args') selected ht := by
            exact Sum.inl.inj (Sum.inr.inj henc')
          exact tagIndex_injective_on hs ht hidx

/-- A finite pattern is child-closed. -/
def ChildClosed (selected : List (RawAns Sigma D.Carrier)) : Prop :=
  forall {f : Sigma.Op}
      {args : Fin (Sigma.arity f) -> RawAns Sigma D.Carrier},
    RawAns.susp f args ∈ selected -> forall i, args i ∈ selected

/-- The selected nodes are normalized. -/
def AllNormal (selected : List (RawAns Sigma D.Carrier)) : Prop :=
  forall s, s ∈ selected -> D.Normal s

/-- Matching uses heterogeneous equality because two operation symbols may
carry different arities until their equality is established. -/
def MatchNode
    (selected : List (RawAns Sigma D.Carrier))
    (f : Sigma.Op)
    (p : Fin (Sigma.arity f) -> FiniteTagCarrier D selected.length)
    (s : RawAns Sigma D.Carrier) : Prop :=
  match s with
  | .old _ => False
  | .susp g args =>
      g = f ∧ HEq (fun i => encode D selected (args i)) p

/-- Finite lookup table for selected suspended nodes. -/
noncomputable def table
    (selected : List (RawAns Sigma D.Carrier))
    (f : Sigma.Op)
    (p : Fin (Sigma.arity f) -> FiniteTagCarrier D selected.length) :
    FiniteTagCarrier D selected.length := by
  classical
  exact if h : Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected ∧ MatchNode D selected f p s then
    encode D selected (Classical.choose h)
  else
    overflow D

/-- Lookup is unambiguous on a child-closed selected pattern. -/
theorem table_hit
    {selected : List (RawAns Sigma D.Carrier)}
    (hclosed : ChildClosed D selected)
    {f : Sigma.Op}
    {args : Fin (Sigma.arity f) -> RawAns Sigma D.Carrier}
    (hs : RawAns.susp f args ∈ selected) :
    table D selected f (fun i => encode D selected (args i)) =
      encode D selected (RawAns.susp f args) := by
  classical
  let hex : Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected ∧
        MatchNode D selected f (fun i => encode D selected (args i)) s :=
    ⟨RawAns.susp f args, hs, by simp [MatchNode]⟩
  unfold table
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have hchosen : Classical.choose hex = RawAns.susp f args := by
    have hmem := hspec.1
    have hmatch := hspec.2
    cases hval : Classical.choose hex with
    | old a =>
        rw [hval] at hmatch
        simp [MatchNode] at hmatch
    | susp g args' =>
        rw [hval] at hmatch hmem
        have hg : g = f := hmatch.1
        subst g
        have hfun :
            (fun i => encode D selected (args' i)) =
              (fun i => encode D selected (args i)) :=
          eq_of_heq hmatch.2
        have hargs : args' = args := by
          funext i
          apply encode_injective_on D (hclosed hmem i) (hclosed hs i)
          exact congrFun hfun i
        cases hargs
        rfl
  rw [hchosen]

/-- A witness that the current encoded input is an old tuple on which the base
operation is defined. -/
structure OldHit
    {selected : List (RawAns Sigma D.Carrier)}
    (f : Sigma.Op)
    (p : Fin (Sigma.arity f) -> FiniteTagCarrier D selected.length) where
  args : Fin (Sigma.arity f) -> D.Carrier
  result : D.Carrier
  eval_eq : D.eval f args = some result
  input_eq : p = fun i => (Sum.inl (args i) : FiniteTagCarrier D selected.length)

/-- Conservative total operation: preserve every old-defined base application
before consulting the finite selected-node table. -/
noncomputable def finiteOp
    (selected : List (RawAns Sigma D.Carrier))
    (f : Sigma.Op)
    (p : Fin (Sigma.arity f) -> FiniteTagCarrier D selected.length) :
    FiniteTagCarrier D selected.length := by
  classical
  exact if h : Nonempty (OldHit D f p) then
    Sum.inl (Classical.choice h).result
  else
    table D selected f p

/-- The conservative operation preserves every defined old application. -/
theorem finiteOp_preserve
    (selected : List (RawAns Sigma D.Carrier))
    (f : Sigma.Op)
    (args : Fin (Sigma.arity f) -> D.Carrier)
    (c : D.Carrier)
    (hbase : D.eval f args = some c) :
    finiteOp D selected f
        (fun i => (Sum.inl (args i) : FiniteTagCarrier D selected.length)) =
      (Sum.inl c : FiniteTagCarrier D selected.length) := by
  classical
  let w : OldHit D f
      (fun i => (Sum.inl (args i) : FiniteTagCarrier D selected.length)) := {
    args := args
    result := c
    eval_eq := hbase
    input_eq := rfl
  }
  have hn : Nonempty (OldHit D f
      (fun i => (Sum.inl (args i) : FiniteTagCarrier D selected.length))) := ⟨w⟩
  unfold finiteOp
  rw [dif_pos hn]
  let z := Classical.choice hn
  have hargs : z.args = args := by
    funext i
    have hi := congrFun z.input_eq i
    exact (Sum.inl.inj hi).symm
  have hres : z.result = c := by
    have hz := z.eval_eq
    rw [hargs, hbase] at hz
    exact (Option.some.inj hz).symm
  exact congrArg Sum.inl hres

noncomputable def patternAlg
    (selected : List (RawAns Sigma D.Carrier)) :
    FiniteTagAlg D selected.length where
  op := finiteOp D selected
  preserve := by
    intro f args c h
    exact finiteOp_preserve D selected f args c h

/-- A selected normalized suspension cannot be mistaken for a defined old
base application. -/
theorem no_old_hit_on_selected_susp
    {selected : List (RawAns Sigma D.Carrier)}
    (hclosed : ChildClosed D selected)
    {f : Sigma.Op}
    {args : Fin (Sigma.arity f) -> RawAns Sigma D.Carrier}
    (hs : RawAns.susp f args ∈ selected)
    (hn : D.Normal (RawAns.susp f args)) :
    ¬ Nonempty (OldHit D f (fun i => encode D selected (args i))) := by
  classical
  intro hhit
  let z := Classical.choice hhit
  have hold : forall i, args i = RawAns.old (z.args i) := by
    intro i
    have hi := congrFun z.input_eq i
    have henc : encode D selected (args i) =
        (Sum.inl (z.args i) : FiniteTagCarrier D selected.length) := hi
    cases harg : args i with
    | old a =>
        rw [harg] at henc
        simp only [encode] at henc
        have ha : a = z.args i := Sum.inl.inj henc
        exact congrArg RawAns.old ha
    | susp g subargs =>
        have hmem : RawAns.susp g subargs ∈ selected := by
          simpa [harg] using hclosed hs i
        rw [harg, encode_susp_of_mem D hmem] at henc
        cases henc
  have hnone := hn.2 z.args hold
  rw [z.eval_eq] at hnone
  contradiction

/-- On a selected normalized suspension, the conservative operation returns
its finite pattern tag. -/
theorem finiteOp_encode_susp
    {selected : List (RawAns Sigma D.Carrier)}
    (hclosed : ChildClosed D selected)
    {f : Sigma.Op}
    {args : Fin (Sigma.arity f) -> RawAns Sigma D.Carrier}
    (hs : RawAns.susp f args ∈ selected)
    (hn : D.Normal (RawAns.susp f args)) :
    finiteOp D selected f (fun i => encode D selected (args i)) =
      encode D selected (RawAns.susp f args) := by
  classical
  have hno := no_old_hit_on_selected_susp D hclosed hs hn
  unfold finiteOp
  rw [dif_neg hno]
  exact table_hit D hclosed hs

/-- The finite observer evaluates every selected normalized node exactly to its
encoding. -/
theorem foldRaw_eq_encode
    {selected : List (RawAns Sigma D.Carrier)}
    (hclosed : ChildClosed D selected) :
    forall (s : RawAns Sigma D.Carrier),
      s ∈ selected -> D.Normal s ->
        FiniteTagAlg.foldRaw (patternAlg D selected) s = encode D selected s := by
  intro s
  induction s with
  | old a =>
      intro hs hn
      rfl
  | susp f args ih =>
      intro hs hn
      change finiteOp D selected f
          (fun i => FiniteTagAlg.foldRaw (patternAlg D selected) (args i)) =
        encode D selected (RawAns.susp f args)
      have hfun :
          (fun i => FiniteTagAlg.foldRaw (patternAlg D selected) (args i)) =
            (fun i => encode D selected (args i)) := by
        funext i
        exact ih i (hclosed hs i) (hn.1 i)
      rw [hfun]
      exact finiteOp_encode_susp D hclosed hs hn

/-- Master finitary finite-pattern realization probe: one compatible
finite-complement observer is injective on every finite child-closed normalized
pattern, for operations of arbitrary finite arity (including arity zero). -/
theorem finitePatternRealization
    (selected : List (RawAns Sigma D.Carrier))
    (hclosed : ChildClosed D selected)
    (hnormal : AllNormal D selected) :
    ∃ T : FiniteTagAlg D selected.length,
      forall {s t : RawAns Sigma D.Carrier},
        s ∈ selected -> t ∈ selected ->
        FiniteTagAlg.foldRaw T s = FiniteTagAlg.foldRaw T t -> s = t := by
  classical
  refine ⟨patternAlg D selected, ?_⟩
  intro s t hs ht heq
  rw [foldRaw_eq_encode D hclosed s hs (hnormal s hs),
      foldRaw_eq_encode D hclosed t ht (hnormal t ht)] at heq
  exact encode_injective_on D hs ht heq

end Proof
end FinitaryPattern
end Resolution
