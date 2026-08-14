import ResolutionExternal

universe u v

namespace Resolution
namespace External

variable {Sigma : Signature.{u}}

namespace FiniteTagProof

variable (D : PartialAlg.{u,v} Sigma)

/-- Preorder enumeration of all nodes of a raw Answer. -/
def subterms : RawAns Sigma D.Carrier -> List (RawAns Sigma D.Carrier)
  | t@(.old _) => [t]
  | t@(.susp _ x y) => t :: (subterms x ++ subterms y)

/-- Constructor count of a raw Answer. -/
def nodeCount : RawAns Sigma D.Carrier -> Nat
  | .old _ => 1
  | .susp _ x y => 1 + (nodeCount x + nodeCount y)

/-- The preorder enumeration contains exactly one entry per constructor
    occurrence, including repeated equal subtrees. -/
@[simp] theorem subterms_length (t : RawAns Sigma D.Carrier) :
    (subterms D t).length = nodeCount D t := by
  induction t with
  | old a =>
      rfl
  | susp f x y ihx ihy =>
      simp [subterms, nodeCount, ihx, ihy, Nat.add_comm]

@[simp] theorem self_mem_subterms (t : RawAns Sigma D.Carrier) :
    t ∈ subterms D t := by
  cases t <;> simp [subterms]

/-- Every child of a selected suspended node is selected as well. -/
theorem children_mem_subterms :
    forall {f : Sigma.Op} {l r t : RawAns Sigma D.Carrier},
      RawAns.susp f l r ∈ subterms D t ->
        l ∈ subterms D t ∧ r ∈ subterms D t := by
  intro f l r t h
  induction t with
  | old a =>
      simp [subterms] at h
  | susp g x y ihx ihy =>
      simp only [subterms, List.mem_cons, List.mem_append] at h
      rcases h with hroot | hx | hy
      · cases hroot
        constructor
        · simp [subterms, self_mem_subterms]
        · simp [subterms, self_mem_subterms]
      · have hc := ihx hx
        constructor
        · simp [subterms, hc.1]
        · simp [subterms, hc.2]
      · have hc := ihy hy
        constructor
        · simp [subterms, hc.1]
        · simp [subterms, hc.2]

/-- The finite list used for a selected pair of roots. -/
def selected (x y : RawAns Sigma D.Carrier) :
    List (RawAns Sigma D.Carrier) :=
  subterms D x ++ subterms D y

/-- The chosen finite tag budget is exactly the sum of the two constructor
    counts. -/
@[simp] theorem selected_length (x y : RawAns Sigma D.Carrier) :
    (selected D x y).length = nodeCount D x + nodeCount D y := by
  simp [selected]

@[simp] theorem left_root_mem_selected (x y : RawAns Sigma D.Carrier) :
    x ∈ selected D x y := by
  simp [selected, self_mem_subterms]

@[simp] theorem right_root_mem_selected (x y : RawAns Sigma D.Carrier) :
    y ∈ selected D x y := by
  simp [selected, self_mem_subterms]

theorem children_mem_selected {x y : RawAns Sigma D.Carrier}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (h : RawAns.susp f l r ∈ selected D x y) :
    l ∈ selected D x y ∧ r ∈ selected D x y := by
  simp only [selected, List.mem_append] at h ⊢
  rcases h with hx | hy
  · have hc := children_mem_subterms D hx
    exact ⟨Or.inl hc.1, Or.inl hc.2⟩
  · have hc := children_mem_subterms D hy
    exact ⟨Or.inr hc.1, Or.inr hc.2⟩

/-- First-occurrence index of an element known to occur in a list. -/
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

/-- Classical finite index, with the equality decider hidden inside the definition. -/
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

/-- The finite tag does not depend on the proof that the node occurs. -/
theorem tagIndex_proof_irrel {a : A} {xs : List A}
    (h₁ h₂ : a ∈ xs) :
    tagIndex a xs h₁ = tagIndex a xs h₂ := by
  rfl

/-- One overflow state, used when no selected transition applies. -/
def overflow {x y : RawAns Sigma D.Carrier} :
    FiniteTagCarrier D (selected D x y).length :=
  Sum.inr (Sum.inr ())

/-- Old leaves keep their old value. Selected suspensions receive their
    first-occurrence finite tag. Everything else goes to overflow. -/
noncomputable def encode (x y : RawAns Sigma D.Carrier) :
    RawAns Sigma D.Carrier ->
      FiniteTagCarrier D (selected D x y).length
  | .old a =>
      (Sum.inl a : FiniteTagCarrier D (selected D x y).length)
  | t@(.susp _ _ _) => by
      classical
      exact if h : t ∈ selected D x y then
        (Sum.inr (Sum.inl (tagIndex t (selected D x y) h)) :
          FiniteTagCarrier D (selected D x y).length)
      else
        overflow D

@[simp] theorem encode_susp_of_mem {x y : RawAns Sigma D.Carrier}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (h : RawAns.susp f l r ∈ selected D x y) :
    encode D x y (RawAns.susp f l r) =
      (Sum.inr (Sum.inl
        (tagIndex (RawAns.susp f l r) (selected D x y) h)) :
          FiniteTagCarrier D (selected D x y).length) := by
  classical
  simp only [encode, dif_pos h]

/-- The encoding is injective on the selected finite closure. -/
theorem encode_injective_on {x y s t : RawAns Sigma D.Carrier}
    (hs : s ∈ selected D x y) (ht : t ∈ selected D x y)
    (henc : encode D x y s = encode D x y t) : s = t := by
  classical
  cases s with
  | old a =>
      cases t with
      | old b =>
          simp only [encode] at henc
          exact congrArg RawAns.old (Sum.inl.inj henc)
      | susp g l r =>
          simp [encode, ht] at henc
  | susp f l r =>
      cases t with
      | old b =>
          simp [encode, hs] at henc
      | susp g l' r' =>
          have henc' := henc
          rw [encode_susp_of_mem D hs, encode_susp_of_mem D ht] at henc'
          have hidx :
              tagIndex (RawAns.susp f l r) (selected D x y) hs =
                tagIndex (RawAns.susp g l' r') (selected D x y) ht := by
            exact Sum.inl.inj (Sum.inr.inj henc')
          exact tagIndex_injective_on hs ht hidx

/-- A selected node matches a finite operation-table entry. -/
def MatchNode (x y : RawAns Sigma D.Carrier) (f : Sigma.Op)
    (p q : FiniteTagCarrier D (selected D x y).length)
    (s : RawAns Sigma D.Carrier) : Prop :=
  match s with
  | .old _ => False
  | .susp g l r =>
      g = f ∧ encode D x y l = p ∧ encode D x y r = q

/-- Finite lookup table. -/
noncomputable def table (x y : RawAns Sigma D.Carrier) (f : Sigma.Op)
    (p q : FiniteTagCarrier D (selected D x y).length) :
    FiniteTagCarrier D (selected D x y).length := by
  classical
  exact if h : Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected D x y ∧ MatchNode D x y f p q s then
    encode D x y (Classical.choose h)
  else
    overflow D

/-- Lookup reproduces every selected suspended node. -/
theorem table_hit {x y : RawAns Sigma D.Carrier}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (hs : RawAns.susp f l r ∈ selected D x y) :
    table D x y f (encode D x y l) (encode D x y r) =
      encode D x y (RawAns.susp f l r) := by
  classical
  let hex : Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ selected D x y ∧
        MatchNode D x y f (encode D x y l) (encode D x y r) s :=
    ⟨RawAns.susp f l r, hs, by simp [MatchNode]⟩
  unfold table
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have hchosen : Classical.choose hex = RawAns.susp f l r := by
    have hmem := hspec.1
    have hmatch := hspec.2
    cases hval : Classical.choose hex with
    | old a =>
        rw [hval] at hmatch
        simp [MatchNode] at hmatch
    | susp g l' r' =>
        rw [hval] at hmatch hmem
        have hm : g = f ∧ encode D x y l' = encode D x y l ∧
            encode D x y r' = encode D x y r := by
          simpa only [MatchNode] using hmatch
        have hc' : l' ∈ selected D x y ∧ r' ∈ selected D x y :=
          children_mem_selected D hmem
        have hc : l ∈ selected D x y ∧ r ∈ selected D x y :=
          children_mem_selected D hs
        have hl : l' = l := encode_injective_on D hc'.1 hc.1 hm.2.1
        have hr : r' = r := encode_injective_on D hc'.2 hc.2 hm.2.2
        cases hm.1
        cases hl
        cases hr
        rfl
  rw [hchosen]

/-- Generated raw Answers are normalized: a suspended old/old application can
    occur only where the old operation is genuinely undefined. -/
def Normal : RawAns Sigma D.Carrier -> Prop
  | .old _ => True
  | .susp f l r =>
      Normal l ∧ Normal r ∧
        forall (a b : D.Carrier), l = .old a -> r = .old b ->
          D.eval f a b = none

theorem normal_liftOp (f : Sigma.Op) {x y : RawAns Sigma D.Carrier}
    (hx : Normal D x) (hy : Normal D y) :
    Normal D (D.liftOp f x y) := by
  cases x with
  | old a =>
      cases y with
      | old b =>
          cases h : D.eval f a b with
          | none =>
              simp only [PartialAlg.liftOp, h]
              exact ⟨hx, hy, by
                intro a' b' ha hb
                cases ha
                cases hb
                exact h⟩
          | some c =>
              simp [PartialAlg.liftOp, h, Normal]
      | susp g y1 y2 =>
          simp only [PartialAlg.liftOp]
          exact ⟨hx, hy, by
            intro a' b' ha hb
            cases hb⟩
  | susp g x1 x2 =>
      simp only [PartialAlg.liftOp]
      exact ⟨hx, hy, by
        intro a' b' ha hb
        cases ha⟩

theorem res_normal (e : Expr Sigma D.Carrier) :
    Normal D (Expr.res D e) := by
  induction e with
  | val a =>
      trivial
  | app f l r ihl ihr =>
      exact normal_liftOp D f ihl ihr

theorem normal_of_mem_subterms {s t : RawAns Sigma D.Carrier}
    (ht : Normal D t) (hs : s ∈ subterms D t) : Normal D s := by
  induction t generalizing s with
  | old a =>
      simp [subterms] at hs
      cases hs
      exact ht
  | susp f l r ihl ihr =>
      simp only [subterms, List.mem_cons, List.mem_append] at hs
      rcases hs with hroot | hl | hr
      · cases hroot
        exact ht
      · exact ihl ht.1 hl
      · exact ihr ht.2.1 hr

theorem normal_of_mem_selected {x y s : RawAns Sigma D.Carrier}
    (hx : Normal D x) (hy : Normal D y)
    (hs : s ∈ selected D x y) : Normal D s := by
  simp only [selected, List.mem_append] at hs
  rcases hs with hs | hs
  · exact normal_of_mem_subterms D hx hs
  · exact normal_of_mem_subterms D hy hs

/-- Conservative operation table: old defined inputs are preserved before any
    finite lookup is attempted. -/
noncomputable def finiteOp (x y : RawAns Sigma D.Carrier) (f : Sigma.Op)
    (p q : FiniteTagCarrier D (selected D x y).length) :
    FiniteTagCarrier D (selected D x y).length :=
  match p, q with
  | Sum.inl a, Sum.inl b =>
      match D.eval f a b with
      | some c => Sum.inl c
      | none => table D x y f p q
  | _, _ => table D x y f p q

noncomputable def separatingAlg (x y : RawAns Sigma D.Carrier) :
    FiniteTagAlg D (selected D x y).length where
  op := finiteOp D x y
  preserve := by
    intro f a b c h
    change (match D.eval f a b with
      | some c' => Sum.inl c'
      | none => table D x y f (Sum.inl a) (Sum.inl b)) = Sum.inl c
    rw [h]

/-- On every selected normalized suspension, the conservative operation table
    returns that suspension's finite tag. -/
theorem finiteOp_encode_susp {x y : RawAns Sigma D.Carrier}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (hs : RawAns.susp f l r ∈ selected D x y)
    (hn : Normal D (RawAns.susp f l r)) :
    finiteOp D x y f (encode D x y l) (encode D x y r) =
      encode D x y (RawAns.susp f l r) := by
  classical
  have htable := table_hit D hs
  cases l with
  | old a =>
      cases r with
      | old b =>
          have hnone : D.eval f a b = none := hn.2.2 a b rfl rfl
          simpa [finiteOp, encode, hnone] using htable
      | susp g r1 r2 =>
          have hrmem := (children_mem_selected D hs).2
          simpa [finiteOp, encode, hrmem] using htable
  | susp g l1 l2 =>
      have hlmem := (children_mem_selected D hs).1
      simpa [finiteOp, encode, hlmem] using htable

/-- The finite model evaluates each selected normalized node to its encoding. -/
theorem foldRaw_eq_encode {x y : RawAns Sigma D.Carrier} :
    forall (s : RawAns Sigma D.Carrier),
      s ∈ selected D x y -> Normal D s ->
        Free.TotalAlg.foldRaw D ((separatingAlg D x y).toTotalAlg D) s =
          encode D x y s := by
  intro s
  induction s with
  | old a =>
      intro hs hn
      rfl
  | susp f l r ihl ihr =>
      intro hs hn
      have hc := children_mem_selected D hs
      change finiteOp D x y f
          (Free.TotalAlg.foldRaw D ((separatingAlg D x y).toTotalAlg D) l)
          (Free.TotalAlg.foldRaw D ((separatingAlg D x y).toTotalAlg D) r) =
        encode D x y (RawAns.susp f l r)
      rw [ihl hc.1 hn.1, ihr hc.2 hn.2.1]
      exact finiteOp_encode_susp D hs hn

end FiniteTagProof

open FiniteTagProof

/-- Finite-tag external semantics separates all generated Answers. -/
theorem finiteTagSeparating_theorem (D : PartialAlg.{u,v} Sigma) :
    FiniteTagSeparating D := by
  classical
  intro x y hall
  rcases x.2 with ⟨ex, hx⟩
  rcases y.2 with ⟨ey, hy⟩
  have nx : Normal D x.1 := by
    rw [← hx]
    exact res_normal D ex
  have ny : Normal D y.1 := by
    rw [← hy]
    exact res_normal D ey
  have hxmem : x.1 ∈ selected D x.1 y.1 :=
    left_root_mem_selected D x.1 y.1
  have hymem : y.1 ∈ selected D x.1 y.1 :=
    right_root_mem_selected D x.1 y.1
  have hmodel := hall (selected D x.1 y.1).length
    (separatingAlg D x.1 y.1)
  change Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 y.1).toTotalAlg D) x.1 =
    Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 y.1).toTotalAlg D) y.1 at hmodel
  rw [foldRaw_eq_encode D x.1 hxmem nx,
      foldRaw_eq_encode D y.1 hymem ny] at hmodel
  have hraw : x.1 = y.1 :=
    encode_injective_on D hxmem hymem hmodel
  exact Subtype.ext hraw

/-- Every distinct generated pair has a separating finite-tag model whose
    finite tag budget is exactly the sum of the two raw constructor counts.
    The carrier additionally contains the original carrier and one overflow
    state. -/
theorem finiteTag_pair_separation_bounded
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (hxy : x ≠ y) :
    ∃ n : Nat,
      n = nodeCount D x.1 + nodeCount D y.1 ∧
      ∃ T : FiniteTagAlg D n,
        Free.TotalAlg.interp D (T.toTotalAlg D) x ≠
          Free.TotalAlg.interp D (T.toTotalAlg D) y := by
  classical
  rcases x.2 with ⟨ex, hx⟩
  rcases y.2 with ⟨ey, hy⟩
  have nx : Normal D x.1 := by
    rw [← hx]
    exact res_normal D ex
  have ny : Normal D y.1 := by
    rw [← hy]
    exact res_normal D ey
  have hxmem : x.1 ∈ selected D x.1 y.1 :=
    left_root_mem_selected D x.1 y.1
  have hymem : y.1 ∈ selected D x.1 y.1 :=
    right_root_mem_selected D x.1 y.1
  refine ⟨(selected D x.1 y.1).length,
    selected_length D x.1 y.1, separatingAlg D x.1 y.1, ?_⟩
  intro hmodel
  change Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 y.1).toTotalAlg D) x.1 =
    Free.TotalAlg.foldRaw D
      ((separatingAlg D x.1 y.1).toTotalAlg D) y.1 at hmodel
  rw [foldRaw_eq_encode D x.1 hxmem nx,
      foldRaw_eq_encode D y.1 hymem ny] at hmodel
  have hraw : x.1 = y.1 :=
    encode_injective_on D hxmem hymem hmodel
  exact hxy (Subtype.ext hraw)

/-- A finite tag budget separates a pair when some preserving finite-tag
    algebra distinguishes their interpretations. -/
def FiniteTagSeparatesAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (n : Nat) : Prop :=
  ∃ T : FiniteTagAlg D n,
    Free.TotalAlg.interp D (T.toTotalAlg D) x ≠
      Free.TotalAlg.interp D (T.toTotalAlg D) y

theorem finiteTagSeparatesAt_symm
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} {n : Nat} :
    FiniteTagSeparatesAt D x y n →
      FiniteTagSeparatesAt D y x n := by
  rintro ⟨T, hT⟩
  exact ⟨T, Ne.symm hT⟩

/-- Bounded well-ordering for natural numbers, proved directly so the rank
    construction does not depend on an additional minimization primitive. -/
theorem exists_least_bounded (p : Nat → Prop) :
    ∀ B : Nat, p B →
      ∃ r : Nat,
        r ≤ B ∧ p r ∧
          ∀ m : Nat, p m → r ≤ m := by
  classical
  intro B
  induction B generalizing p with
  | zero =>
      intro hB
      exact ⟨0, Nat.le_refl 0, hB,
        fun m hm => Nat.zero_le m⟩
  | succ B ih =>
      intro hB
      by_cases h0 : p 0
      · exact ⟨0, Nat.zero_le _, h0,
          fun m hm => Nat.zero_le m⟩
      · let q : Nat → Prop := fun n => p (Nat.succ n)
        have hqB : q B := by
          exact hB
        rcases ih q hqB with ⟨r, hrB, hqr, hmin⟩
        refine ⟨Nat.succ r, Nat.succ_le_succ hrB, ?_, ?_⟩
        · exact hqr
        · intro m hm
          cases m with
          | zero =>
              exact False.elim (h0 hm)
          | succ m =>
              apply Nat.succ_le_succ
              apply hmin m
              exact hm

theorem finiteTagSeparatesAt_size_bound
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (hxy : x ≠ y) :
    FiniteTagSeparatesAt D x y
      (nodeCount D x.1 + nodeCount D y.1) := by
  rcases finiteTag_pair_separation_bounded D x y hxy with
    ⟨n, hn, T, hT⟩
  subst n
  exact ⟨T, hT⟩

theorem finiteSeparationRank_witness_exists
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (hxy : x ≠ y) :
    ∃ r : Nat,
      r ≤ nodeCount D x.1 + nodeCount D y.1 ∧
      FiniteTagSeparatesAt D x y r ∧
      ∀ m : Nat, FiniteTagSeparatesAt D x y m → r ≤ m := by
  exact exists_least_bounded
    (p := FiniteTagSeparatesAt D x y)
    (nodeCount D x.1 + nodeCount D y.1)
    (finiteTagSeparatesAt_size_bound D x y hxy)

/-- The finite separation rank is the least number of finite tags needed to
    distinguish a pair. Equal pairs receive rank zero by convention. -/
noncomputable def finiteSeparationRank
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : Nat := by
  classical
  exact if h : x ≠ y then
    Classical.choose (finiteSeparationRank_witness_exists D x y h)
  else
    0

@[simp] theorem finiteSeparationRank_eq_zero_of_eq
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x = y) :
    finiteSeparationRank D x y = 0 := by
  classical
  subst y
  simp [finiteSeparationRank]

theorem finiteSeparationRank_separates
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    FiniteTagSeparatesAt D x y
      (finiteSeparationRank D x y) := by
  classical
  have hspec :=
    Classical.choose_spec
      (finiteSeparationRank_witness_exists D x y hxy)
  simpa [finiteSeparationRank, hxy] using hspec.2.1

theorem finiteSeparationRank_minimal
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hn : FiniteTagSeparatesAt D x y n) :
    finiteSeparationRank D x y ≤ n := by
  classical
  have hspec :=
    Classical.choose_spec
      (finiteSeparationRank_witness_exists D x y hxy)
  simpa [finiteSeparationRank, hxy] using hspec.2.2 n hn

theorem finiteSeparationRank_le_size
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    finiteSeparationRank D x y ≤
      nodeCount D x.1 + nodeCount D y.1 := by
  classical
  have hspec :=
    Classical.choose_spec
      (finiteSeparationRank_witness_exists D x y hxy)
  simpa [finiteSeparationRank, hxy] using hspec.1

theorem finiteSeparationRank_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    finiteSeparationRank D x y =
      finiteSeparationRank D y x := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    apply Nat.le_antisymm
    · apply finiteSeparationRank_minimal D hxy
      exact finiteTagSeparatesAt_symm D
        (finiteSeparationRank_separates D hyx)
    · apply finiteSeparationRank_minimal D hyx
      exact finiteTagSeparatesAt_symm D
        (finiteSeparationRank_separates D hxy)
/-- The auxiliary-state cost counts the least finite tags needed for a
    separating model together with the single overflow state. Equal pairs have
    cost zero. -/
noncomputable def finiteAuxiliaryCost
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : Nat := by
  classical
  exact if h : x ≠ y then
    Nat.succ (finiteSeparationRank D x y)
  else
    0

@[simp] theorem finiteAuxiliaryCost_eq_zero_of_eq
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x = y) :
    finiteAuxiliaryCost D x y = 0 := by
  classical
  subst y
  simp [finiteAuxiliaryCost]

@[simp] theorem finiteAuxiliaryCost_of_ne
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    finiteAuxiliaryCost D x y =
      Nat.succ (finiteSeparationRank D x y) := by
  classical
  simp [finiteAuxiliaryCost, hxy]

theorem finiteAuxiliaryCost_eq_zero_iff
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    finiteAuxiliaryCost D x y = 0 ↔ x = y := by
  classical
  constructor
  · intro hcost
    by_cases hxy : x = y
    · exact hxy
    · have hsucc : Nat.succ (finiteSeparationRank D x y) = 0 := by
        simpa [finiteAuxiliaryCost, hxy] using hcost
      exact False.elim (Nat.succ_ne_zero _ hsucc)
  · intro hxy
    subst y
    simp [finiteAuxiliaryCost]

theorem finiteAuxiliaryCost_positive
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    1 ≤ finiteAuxiliaryCost D x y := by
  rw [finiteAuxiliaryCost_of_ne D hxy]
  exact Nat.succ_le_succ (Nat.zero_le _)

theorem finiteAuxiliaryCost_attained
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    ∃ n : Nat,
      n + 1 = finiteAuxiliaryCost D x y ∧
      FiniteTagSeparatesAt D x y n := by
  refine ⟨finiteSeparationRank D x y, ?_, ?_⟩
  · simp [finiteAuxiliaryCost, hxy, Nat.succ_eq_add_one]
  · exact finiteSeparationRank_separates D hxy

theorem finiteAuxiliaryCost_minimal
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hn : FiniteTagSeparatesAt D x y n) :
    finiteAuxiliaryCost D x y ≤ n + 1 := by
  rw [finiteAuxiliaryCost_of_ne D hxy]
  simpa [Nat.succ_eq_add_one] using
    Nat.succ_le_succ (finiteSeparationRank_minimal D hxy hn)

theorem finiteAuxiliaryCost_le_size_of_ne
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    finiteAuxiliaryCost D x y ≤
      nodeCount D x.1 + nodeCount D y.1 + 1 := by
  rw [finiteAuxiliaryCost_of_ne D hxy]
  simpa [Nat.succ_eq_add_one] using
    Nat.succ_le_succ (finiteSeparationRank_le_size D hxy)

theorem finiteAuxiliaryCost_le_size
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    finiteAuxiliaryCost D x y ≤
      nodeCount D x.1 + nodeCount D y.1 + 1 := by
  classical
  by_cases hxy : x = y
  · rw [finiteAuxiliaryCost_eq_zero_of_eq D hxy]
    exact Nat.zero_le _
  · exact finiteAuxiliaryCost_le_size_of_ne D hxy

theorem finiteAuxiliaryCost_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    finiteAuxiliaryCost D x y =
      finiteAuxiliaryCost D y x := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    simp [finiteAuxiliaryCost, hxy, hyx,
      finiteSeparationRank_symm D x y]
/-- Embed a smaller finite tag space into a larger one. -/
def padFin {n m : Nat} (h : n ≤ m) (i : Fin n) : Fin m :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/-- Embed a finite-tag carrier into one with additional unused tags. -/
def padCarrier
    (D : PartialAlg.{u,v} Sigma) {n m : Nat} (h : n ≤ m) :
    FiniteTagCarrier D n → FiniteTagCarrier D m
  | Sum.inl a => Sum.inl a
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (padFin h i))
  | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr u)

/-- Project a larger finite-tag carrier back to the original one. Additional
    tags are sent to overflow. -/
def unpadCarrier
    (D : PartialAlg.{u,v} Sigma) {n m : Nat} (h : n ≤ m) :
    FiniteTagCarrier D m → FiniteTagCarrier D n
  | Sum.inl a => Sum.inl a
  | Sum.inr (Sum.inl j) =>
      if hj : j.val < n then
        Sum.inr (Sum.inl ⟨j.val, hj⟩)
      else
        Sum.inr (Sum.inr ())
  | Sum.inr (Sum.inr u) => Sum.inr (Sum.inr u)

@[simp] theorem unpadCarrier_padCarrier
    (D : PartialAlg.{u,v} Sigma) {n m : Nat} (h : n ≤ m)
    (s : FiniteTagCarrier D n) :
    unpadCarrier D h (padCarrier D h s) = s := by
  cases s with
  | inl a =>
      rfl
  | inr s =>
      cases s with
      | inl i =>
          simp [padCarrier, unpadCarrier, padFin, i.isLt]
      | inr u =>
          cases u
          rfl

/-- A finite-tag algebra remains preserving after adding unused tags. -/
def padFiniteTagAlg
    (D : PartialAlg.{u,v} Sigma) {n m : Nat}
    (T : FiniteTagAlg D n) (h : n ≤ m) :
    FiniteTagAlg D m where
  op f x y :=
    padCarrier D h
      (T.op f (unpadCarrier D h x) (unpadCarrier D h y))
  preserve := by
    intro f a b c heval
    change padCarrier D h
      (T.op f (Sum.inl a) (Sum.inl b)) = Sum.inl c
    rw [T.preserve f a b c heval]
    rfl

/-- Interpretation commutes with finite-tag padding. -/
theorem foldRaw_padFiniteTagAlg
    (D : PartialAlg.{u,v} Sigma) {n m : Nat}
    (T : FiniteTagAlg D n) (h : n ≤ m) :
    ∀ s : RawAns Sigma D.Carrier,
      Free.TotalAlg.foldRaw D ((padFiniteTagAlg D T h).toTotalAlg D) s =
        padCarrier D h
          (Free.TotalAlg.foldRaw D (T.toTotalAlg D) s) := by
  intro s
  induction s with
  | old a =>
      rfl
  | susp f l r ihl ihr =>
      change
        padCarrier D h
          (T.op f
            (unpadCarrier D h
              (Free.TotalAlg.foldRaw D
                ((padFiniteTagAlg D T h).toTotalAlg D) l))
            (unpadCarrier D h
              (Free.TotalAlg.foldRaw D
                ((padFiniteTagAlg D T h).toTotalAlg D) r))) =
          padCarrier D h
            (T.op f
              (Free.TotalAlg.foldRaw D (T.toTotalAlg D) l)
              (Free.TotalAlg.foldRaw D (T.toTotalAlg D) r))
      rw [ihl, ihr,
        unpadCarrier_padCarrier D h,
        unpadCarrier_padCarrier D h]

@[simp] theorem interp_padFiniteTagAlg
    (D : PartialAlg.{u,v} Sigma) {n m : Nat}
    (T : FiniteTagAlg D n) (h : n ≤ m)
    (x : Free.GeneratedAns D) :
    Free.TotalAlg.interp D ((padFiniteTagAlg D T h).toTotalAlg D) x =
      padCarrier D h
        (Free.TotalAlg.interp D (T.toTotalAlg D) x) := by
  exact foldRaw_padFiniteTagAlg D T h x.1

/-- Separation is upward closed in the number of available finite tags. -/
theorem finiteTagSeparatesAt_mono
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} {n m : Nat}
    (hnm : n ≤ m) :
    FiniteTagSeparatesAt D x y n →
      FiniteTagSeparatesAt D x y m := by
  rintro ⟨T, hT⟩
  refine ⟨padFiniteTagAlg D T hnm, ?_⟩
  intro hEq
  apply hT
  rw [interp_padFiniteTagAlg D T hnm x,
      interp_padFiniteTagAlg D T hnm y] at hEq
  have hEq' := congrArg (unpadCarrier D hnm) hEq
  rw [unpadCarrier_padCarrier D hnm,
      unpadCarrier_padCarrier D hnm] at hEq'
  exact hEq'

/-- For distinct Answers, the separation rank is the exact threshold: a budget
    separates precisely when it is at least the rank. -/
theorem finiteTagSeparatesAt_iff_rank_le
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    (n : Nat) :
    FiniteTagSeparatesAt D x y n ↔
      finiteSeparationRank D x y ≤ n := by
  constructor
  · intro hn
    exact finiteSeparationRank_minimal D hxy hn
  · intro hrank
    exact finiteTagSeparatesAt_mono D hrank
      (finiteSeparationRank_separates D hxy)

/-- Equivalently, a budget of `n` tags separates exactly when its `n + 1`
    auxiliary states cover the minimal auxiliary-state cost. -/
theorem finiteTagSeparatesAt_iff_auxiliaryCost_le
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    (n : Nat) :
    FiniteTagSeparatesAt D x y n ↔
      finiteAuxiliaryCost D x y ≤ n + 1 := by
  simpa [finiteAuxiliaryCost_of_ne D hxy,
    Nat.succ_eq_add_one] using
      (finiteTagSeparatesAt_iff_rank_le D hxy n)
/-- Indistinguishability by every preserving finite-tag algebra with exactly
    `n` available tags. -/
def FiniteTagEqAt
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) : Prop :=
  ∀ T : FiniteTagAlg D n,
    Free.TotalAlg.interp D (T.toTotalAlg D) x =
      Free.TotalAlg.interp D (T.toTotalAlg D) y

@[refl] theorem finiteTagEqAt_refl
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x : Free.GeneratedAns D) :
    FiniteTagEqAt D n x x := by
  intro T
  rfl

@[symm] theorem finiteTagEqAt_symm
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y : Free.GeneratedAns D} :
    FiniteTagEqAt D n x y →
      FiniteTagEqAt D n y x := by
  intro h T
  exact Eq.symm (h T)

theorem finiteTagEqAt_trans
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y z : Free.GeneratedAns D} :
    FiniteTagEqAt D n x y →
      FiniteTagEqAt D n y z →
        FiniteTagEqAt D n x z := by
  intro hxy hyz T
  exact Eq.trans (hxy T) (hyz T)

/-- At a fixed budget, universal agreement is exactly the negation of
    pair-separation at that budget. -/
theorem finiteTagEqAt_iff_not_separatesAt
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) :
    FiniteTagEqAt D n x y ↔
      ¬ FiniteTagSeparatesAt D x y n := by
  classical
  constructor
  · intro hEq hSep
    rcases hSep with ⟨T, hT⟩
    exact hT (hEq T)
  · intro hNo T
    by_cases hEq :
        Free.TotalAlg.interp D (T.toTotalAlg D) x =
          Free.TotalAlg.interp D (T.toTotalAlg D) y
    · exact hEq
    · exact False.elim (hNo ⟨T, hEq⟩)

/-- The finite observational relations form a descending filtration: agreement
    for every larger-budget model implies agreement at every smaller budget. -/
theorem finiteTagEqAt_antitone
    (D : PartialAlg.{u,v} Sigma)
    {n m : Nat} (hnm : n ≤ m)
    {x y : Free.GeneratedAns D} :
    FiniteTagEqAt D m x y →
      FiniteTagEqAt D n x y := by
  intro hEqM
  apply (finiteTagEqAt_iff_not_separatesAt D n x y).2
  intro hSepN
  have hSepM : FiniteTagSeparatesAt D x y m :=
    finiteTagSeparatesAt_mono D hnm hSepN
  exact (finiteTagEqAt_iff_not_separatesAt D m x y).1 hEqM hSepM

/-- The original all-finite-model relation is the intersection of the fixed
    budget relations. -/
theorem finiteTagEq_iff_forall_finiteTagEqAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    FiniteTagEq D x y ↔
      ∀ n : Nat, FiniteTagEqAt D n x y := by
  rfl

/-- The observational filtration is Hausdorff: agreement at every finite
    budget is equality of generated Answers. -/
theorem forall_finiteTagEqAt_iff_eq
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    (∀ n : Nat, FiniteTagEqAt D n x y) ↔ x = y := by
  constructor
  · intro hall
    apply finiteTagSeparating_theorem D
    intro n T
    exact hall n T
  · intro hxy
    subst y
    intro n T
    rfl

/-- For a distinct pair, fixed-budget indistinguishability holds exactly below
    the finite separation rank. -/
theorem finiteTagEqAt_iff_lt_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    (n : Nat) :
    FiniteTagEqAt D n x y ↔
      n < finiteSeparationRank D x y := by
  constructor
  · intro hEq
    apply Nat.lt_of_not_ge
    intro hRank
    have hSep : FiniteTagSeparatesAt D x y n :=
      (finiteTagSeparatesAt_iff_rank_le D hxy n).2 hRank
    exact (finiteTagEqAt_iff_not_separatesAt D n x y).1 hEq hSep
  · intro hlt
    apply (finiteTagEqAt_iff_not_separatesAt D n x y).2
    intro hSep
    have hRank : finiteSeparationRank D x y ≤ n :=
      (finiteTagSeparatesAt_iff_rank_le D hxy n).1 hSep
    exact (Nat.not_le_of_gt hlt) hRank

/-- Uniform form of the filtration law, including equal pairs. -/
theorem finiteTagEqAt_iff_eq_or_lt_rank
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat) (x y : Free.GeneratedAns D) :
    FiniteTagEqAt D n x y ↔
      x = y ∨ n < finiteSeparationRank D x y := by
  classical
  by_cases hxy : x = y
  · subst y
    constructor
    · intro hEq
      exact Or.inl rfl
    · intro h
      exact finiteTagEqAt_refl D n x
  · constructor
    · intro hEq
      exact Or.inr ((finiteTagEqAt_iff_lt_rank D hxy n).1 hEq)
    · intro h
      cases h with
      | inl heq =>
          exact False.elim (hxy heq)
      | inr hlt =>
          exact (finiteTagEqAt_iff_lt_rank D hxy n).2 hlt

/-- A distinct pair becomes distinguishable exactly at the rank itself. -/
theorem not_finiteTagEqAt_at_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    ¬ FiniteTagEqAt D (finiteSeparationRank D x y) x y := by
  intro hEq
  have hlt :=
    (finiteTagEqAt_iff_lt_rank D hxy
      (finiteSeparationRank D x y)).1 hEq
  exact Nat.lt_irrefl _ hlt

/-- Every budget strictly below the rank still identifies the pair. -/
theorem finiteTagEqAt_of_lt_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hn : n < finiteSeparationRank D x y) :
    FiniteTagEqAt D n x y :=
  (finiteTagEqAt_iff_lt_rank D hxy n).2 hn

/-- Every budget at or above the rank distinguishes the pair. -/
theorem not_finiteTagEqAt_of_rank_le
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hn : finiteSeparationRank D x y ≤ n) :
    ¬ FiniteTagEqAt D n x y := by
  intro hEq
  have hlt := (finiteTagEqAt_iff_lt_rank D hxy n).1 hEq
  exact (Nat.not_le_of_gt hlt) hn

/-- If the rank is a successor, the pair lies together at the immediately
    preceding stage and separates at the next stage. -/
theorem finiteTagEqAt_rank_boundary
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hrank : finiteSeparationRank D x y = Nat.succ n) :
    FiniteTagEqAt D n x y ∧
      ¬ FiniteTagEqAt D (Nat.succ n) x y := by
  constructor
  · apply finiteTagEqAt_of_lt_rank D hxy
    rw [hrank]
    exact Nat.lt_succ_self n
  · apply not_finiteTagEqAt_of_rank_le D hxy
    rw [hrank]
    exact Nat.le_refl _
/-- Equivalent centers determine the same finite observational class. -/
theorem finiteTagEqAt_left_congr
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y z : Free.GeneratedAns D}
    (hxy : FiniteTagEqAt D n x y) :
    FiniteTagEqAt D n x z ↔
      FiniteTagEqAt D n y z := by
  constructor
  · intro hxz
    exact finiteTagEqAt_trans D n
      (finiteTagEqAt_symm D n hxy) hxz
  · intro hyz
    exact finiteTagEqAt_trans D n hxy hyz

/-- The same class-invariance holds in the right argument. -/
theorem finiteTagEqAt_right_congr
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y z : Free.GeneratedAns D}
    (hxy : FiniteTagEqAt D n x y) :
    FiniteTagEqAt D n z x ↔
      FiniteTagEqAt D n z y := by
  constructor
  · intro hzx
    exact finiteTagEqAt_trans D n hzx hxy
  · intro hzy
    exact finiteTagEqAt_trans D n hzy
      (finiteTagEqAt_symm D n hxy)

/-- Two finite observational classes that share a point coincide. -/
theorem finiteTagEqAt_classes_coincide_of_common_point
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y z : Free.GeneratedAns D}
    (hxz : FiniteTagEqAt D n x z)
    (hyz : FiniteTagEqAt D n y z) :
    FiniteTagEqAt D n x y ∧
      ∀ w : Free.GeneratedAns D,
        FiniteTagEqAt D n x w ↔
          FiniteTagEqAt D n y w := by
  have hxy : FiniteTagEqAt D n x y :=
    finiteTagEqAt_trans D n hxz
      (finiteTagEqAt_symm D n hyz)
  exact ⟨hxy, fun w => finiteTagEqAt_left_congr D n hxy⟩

/-- Non-Archimedean similarity law for separation difficulty. For unequal
    endpoints, the rank of the outer pair is at least the smaller rank of the
    two legs. -/
theorem finiteSeparationRank_min_triangle
    (D : PartialAlg.{u,v} Sigma)
    (x y z : Free.GeneratedAns D) (hxz : x ≠ z) :
    Nat.min (finiteSeparationRank D x y)
        (finiteSeparationRank D y z) ≤
      finiteSeparationRank D x z := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hyz : y = z
    · subst z
      simp
    · by_cases hle :
          Nat.min (finiteSeparationRank D x y)
              (finiteSeparationRank D y z) ≤
            finiteSeparationRank D x z
      · exact hle
      · have hltMin :
            finiteSeparationRank D x z <
              Nat.min (finiteSeparationRank D x y)
                (finiteSeparationRank D y z) :=
          Nat.lt_of_not_ge hle
        have hltXY :
            finiteSeparationRank D x z <
              finiteSeparationRank D x y :=
          Nat.lt_of_lt_of_le hltMin
            (Nat.min_le_left _ _)
        have hltYZ :
            finiteSeparationRank D x z <
              finiteSeparationRank D y z :=
          Nat.lt_of_lt_of_le hltMin
            (Nat.min_le_right _ _)
        have hEqXY :
            FiniteTagEqAt D (finiteSeparationRank D x z) x y :=
          finiteTagEqAt_of_lt_rank D hxy hltXY
        have hEqYZ :
            FiniteTagEqAt D (finiteSeparationRank D x z) y z :=
          finiteTagEqAt_of_lt_rank D hyz hltYZ
        have hEqXZ :
            FiniteTagEqAt D (finiteSeparationRank D x z) x z :=
          finiteTagEqAt_trans D
            (finiteSeparationRank D x z) hEqXY hEqYZ
        exact False.elim
          ((not_finiteTagEqAt_at_rank D hxz) hEqXZ)

/-- Ultrametric isosceles law: when one leg has strictly greater separation
    rank than the other, the outer pair has exactly the smaller rank. -/
theorem finiteSeparationRank_eq_left_of_lt_right
    (D : PartialAlg.{u,v} Sigma)
    {x y z : Free.GeneratedAns D}
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hRank : finiteSeparationRank D x y <
      finiteSeparationRank D y z) :
    finiteSeparationRank D x z =
      finiteSeparationRank D x y := by
  have hLower :
      finiteSeparationRank D x y ≤
        finiteSeparationRank D x z := by
    have hTriangle :=
      finiteSeparationRank_min_triangle D x y z hxz
    have hLeg : finiteSeparationRank D x y ≤
        finiteSeparationRank D y z :=
      Nat.le_of_lt hRank
    simpa [Nat.min_def, hLeg] using hTriangle
  have hOtherTriangle :=
    finiteSeparationRank_min_triangle D x z y hxy
  rw [finiteSeparationRank_symm D z y] at hOtherTriangle
  rcases Nat.le_total (finiteSeparationRank D x z)
      (finiteSeparationRank D y z) with hXZ | hYZ
  · have hUpper :
        finiteSeparationRank D x z ≤
          finiteSeparationRank D x y := by
      simpa [Nat.min_def, hXZ] using hOtherTriangle
    exact Nat.le_antisymm hUpper hLower
  · have hBad :
        finiteSeparationRank D y z ≤
          finiteSeparationRank D x y := by
      simpa [Nat.min_def, hYZ] using hOtherTriangle
    exact False.elim
      ((Nat.not_le_of_gt hRank) hBad)
/-- Extended observational depth. Finite values record separation rank; infinity
    is reserved for equality. -/
inductive SeparationDepth where
  | finite (n : Nat)
  | infinity
  deriving DecidableEq

namespace SeparationDepth

/-- Natural order extended by a greatest element `infinity`. -/
def le : SeparationDepth → SeparationDepth → Prop
  | .finite m, .finite n => m ≤ n
  | .finite _, .infinity => True
  | .infinity, .finite _ => False
  | .infinity, .infinity => True

/-- Minimum in the extended natural order. -/
def min : SeparationDepth → SeparationDepth → SeparationDepth
  | .infinity, b => b
  | a, .infinity => a
  | .finite m, .finite n => .finite (Nat.min m n)

@[simp] theorem le_finite_finite (m n : Nat) :
    le (.finite m) (.finite n) ↔ m ≤ n := by
  rfl

@[simp] theorem le_finite_infinity (n : Nat) :
    le (.finite n) .infinity := by
  trivial

@[simp] theorem not_le_infinity_finite (n : Nat) :
    ¬ le .infinity (.finite n) := by
  intro h
  exact h

@[simp] theorem le_infinity_infinity :
    le .infinity .infinity := by
  trivial

@[simp] theorem min_infinity_left (a : SeparationDepth) :
    min .infinity a = a := by
  rfl

@[simp] theorem min_infinity_right (a : SeparationDepth) :
    min a .infinity = a := by
  cases a <;> rfl

@[simp] theorem min_finite_finite (m n : Nat) :
    min (.finite m) (.finite n) = .finite (Nat.min m n) := by
  rfl

theorem le_refl (a : SeparationDepth) : le a a := by
  cases a with
  | finite n => exact Nat.le_refl n
  | infinity => trivial

theorem le_trans {a b c : SeparationDepth} :
    le a b → le b c → le a c := by
  intro hab hbc
  cases a with
  | finite a =>
      cases b with
      | finite b =>
          cases c with
          | finite c => exact Nat.le_trans hab hbc
          | infinity => trivial
      | infinity =>
          cases c with
          | finite c => exact False.elim hbc
          | infinity => trivial
  | infinity =>
      cases b with
      | finite b => exact False.elim hab
      | infinity =>
          cases c with
          | finite c => exact False.elim hbc
          | infinity => trivial

theorem le_antisymm {a b : SeparationDepth} :
    le a b → le b a → a = b := by
  intro hab hba
  cases a with
  | finite a =>
      cases b with
      | finite b =>
          exact congrArg SeparationDepth.finite
            (Nat.le_antisymm hab hba)
      | infinity => exact False.elim hba
  | infinity =>
      cases b with
      | finite b => exact False.elim hab
      | infinity => rfl

theorem le_total (a b : SeparationDepth) :
    le a b ∨ le b a := by
  cases a with
  | finite a =>
      cases b with
      | finite b =>
          rcases Nat.le_total a b with hab | hba
          · exact Or.inl hab
          · exact Or.inr hba
      | infinity => exact Or.inl True.intro
  | infinity =>
      cases b with
      | finite b => exact Or.inr True.intro
      | infinity => exact Or.inl True.intro

theorem min_le_left (a b : SeparationDepth) :
    le (min a b) a := by
  cases a with
  | finite a =>
      cases b with
      | finite b => exact Nat.min_le_left a b
      | infinity => exact Nat.le_refl a
  | infinity =>
      cases b <;> trivial

theorem min_le_right (a b : SeparationDepth) :
    le (min a b) b := by
  cases a with
  | finite a =>
      cases b with
      | finite b => exact Nat.min_le_right a b
      | infinity => trivial
  | infinity =>
      cases b with
      | finite b => exact Nat.le_refl b
      | infinity => trivial

end SeparationDepth

/-- Total observational depth: equal Answers have infinite depth; distinct
    Answers have their finite separation rank. -/
noncomputable def observationalDepth
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : SeparationDepth := by
  classical
  exact if h : x = y then
    .infinity
  else
    .finite (finiteSeparationRank D x y)

@[simp] theorem observationalDepth_self
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    observationalDepth D x x = .infinity := by
  classical
  simp [observationalDepth]

@[simp] theorem observationalDepth_of_ne
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    observationalDepth D x y =
      .finite (finiteSeparationRank D x y) := by
  classical
  simp [observationalDepth, hxy]

theorem observationalDepth_eq_infinity_iff
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    observationalDepth D x y = .infinity ↔ x = y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [observationalDepth]
  · simp [observationalDepth, hxy]

theorem observationalDepth_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    observationalDepth D x y =
      observationalDepth D y x := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    simp [observationalDepth, hxy, hyx,
      finiteSeparationRank_symm D x y]

/-- Total non-Archimedean law: the depth of the outer pair is at least the
    minimum depth of the two legs, including all equality cases. -/
theorem observationalDepth_min_triangle
    (D : PartialAlg.{u,v} Sigma)
    (x y z : Free.GeneratedAns D) :
    SeparationDepth.le
      (SeparationDepth.min
        (observationalDepth D x y)
        (observationalDepth D y z))
      (observationalDepth D x z) := by
  classical
  by_cases hxz : x = z
  · subst z
    by_cases hxy : x = y
    · subst y
      simp [observationalDepth,
        SeparationDepth.min, SeparationDepth.le]
    · have hyx : y ≠ x := Ne.symm hxy
      simp [observationalDepth, hxy, hyx,
        SeparationDepth.min, SeparationDepth.le]
  · by_cases hxy : x = y
    · subst y
      simp [observationalDepth, hxz,
        SeparationDepth.min, SeparationDepth.le]
    · by_cases hyz : y = z
      · subst z
        simp [observationalDepth, hxy,
          SeparationDepth.min, SeparationDepth.le]
      · simpa [observationalDepth, hxy, hyz, hxz,
          SeparationDepth.min, SeparationDepth.le] using
          (finiteSeparationRank_min_triangle D x y z hxz)

/-- Abstract non-Archimedean similarity space valued in extended natural
    depth. -/
structure NonArchimedeanSimilarity (X : Type w) where
  depth : X → X → SeparationDepth
  eq_infinity : ∀ x y, depth x y = .infinity ↔ x = y
  symm : ∀ x y, depth x y = depth y x
  min_triangle : ∀ x y z,
    SeparationDepth.le
      (SeparationDepth.min (depth x y) (depth y z))
      (depth x z)

/-- Generated Answers with finite-tag semantics form a non-Archimedean
    similarity space. -/
noncomputable def finiteTagNonArchimedeanSimilarity
    (D : PartialAlg.{u,v} Sigma) :
    NonArchimedeanSimilarity (Free.GeneratedAns D) where
  depth := observationalDepth D
  eq_infinity := observationalDepth_eq_infinity_iff D
  symm := observationalDepth_symm D
  min_triangle := observationalDepth_min_triangle D
/-- Symbolic discrete distance. `level n` represents the scale determined by
    separation rank `n`; greater ranks are smaller distances. -/
inductive SeparationDistance where
  | zero
  | level (n : Nat)
  deriving DecidableEq

namespace SeparationDistance

/-- Distance order: zero is least and finite levels are ordered contravariantly
    by separation rank. -/
def le : SeparationDistance → SeparationDistance → Prop
  | .zero, _ => True
  | .level _, .zero => False
  | .level m, .level n => n ≤ m

/-- Maximum distance in the contravariant rank order. -/
def max : SeparationDistance → SeparationDistance → SeparationDistance
  | .zero, b => b
  | a, .zero => a
  | .level m, .level n => .level (Nat.min m n)

/-- Convert extended similarity depth into zero-based distance. -/
def ofDepth : SeparationDepth → SeparationDistance
  | .infinity => .zero
  | .finite n => .level n

@[simp] theorem le_zero (a : SeparationDistance) :
    le .zero a := by
  trivial

@[simp] theorem not_le_level_zero (n : Nat) :
    ¬ le (.level n) .zero := by
  intro h
  exact h

@[simp] theorem le_level_level (m n : Nat) :
    le (.level m) (.level n) ↔ n ≤ m := by
  rfl

@[simp] theorem max_zero_left (a : SeparationDistance) :
    max .zero a = a := by
  rfl

@[simp] theorem max_zero_right (a : SeparationDistance) :
    max a .zero = a := by
  cases a <;> rfl

@[simp] theorem max_level_level (m n : Nat) :
    max (.level m) (.level n) = .level (Nat.min m n) := by
  rfl

@[simp] theorem ofDepth_infinity :
    ofDepth .infinity = .zero := by
  rfl

@[simp] theorem ofDepth_finite (n : Nat) :
    ofDepth (.finite n) = .level n := by
  rfl

theorem le_refl (a : SeparationDistance) : le a a := by
  cases a with
  | zero => trivial
  | level n => exact Nat.le_refl n

theorem le_trans {a b c : SeparationDistance} :
    le a b → le b c → le a c := by
  intro hab hbc
  cases a with
  | zero => trivial
  | level a =>
      cases b with
      | zero => exact False.elim hab
      | level b =>
          cases c with
          | zero => exact False.elim hbc
          | level c => exact Nat.le_trans hbc hab

theorem le_antisymm {a b : SeparationDistance} :
    le a b → le b a → a = b := by
  intro hab hba
  cases a with
  | zero =>
      cases b with
      | zero => rfl
      | level b => exact False.elim hba
  | level a =>
      cases b with
      | zero => exact False.elim hab
      | level b =>
          exact congrArg SeparationDistance.level
            (Nat.le_antisymm hba hab)

theorem le_total (a b : SeparationDistance) :
    le a b ∨ le b a := by
  cases a with
  | zero => exact Or.inl True.intro
  | level a =>
      cases b with
      | zero => exact Or.inr True.intro
      | level b =>
          rcases Nat.le_total a b with hab | hba
          · exact Or.inr hab
          · exact Or.inl hba

theorem le_max_left (a b : SeparationDistance) :
    le a (max a b) := by
  cases a with
  | zero => trivial
  | level a =>
      cases b with
      | zero => exact Nat.le_refl a
      | level b => exact Nat.min_le_left a b

theorem le_max_right (a b : SeparationDistance) :
    le b (max a b) := by
  cases a with
  | zero => exact le_refl b
  | level a =>
      cases b with
      | zero => trivial
      | level b => exact Nat.min_le_right a b

/-- The extended-depth minimum law is exactly the strong triangle law after
    converting depth into distance. -/
theorem ofDepth_strong_triangle
    {a b c : SeparationDepth}
    (h : SeparationDepth.le (SeparationDepth.min a b) c) :
    le (ofDepth c) (max (ofDepth a) (ofDepth b)) := by
  cases a <;> cases b <;> cases c <;>
    simpa [SeparationDepth.min, SeparationDepth.le,
      ofDepth, max, le] using h

end SeparationDistance

/-- Canonical symbolic ultrametric induced by finite observational semantics. -/
noncomputable def observationalDistance
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : SeparationDistance :=
  SeparationDistance.ofDepth (observationalDepth D x y)

@[simp] theorem observationalDistance_self
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    observationalDistance D x x = .zero := by
  simp [observationalDistance]

@[simp] theorem observationalDistance_of_ne
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    observationalDistance D x y =
      .level (finiteSeparationRank D x y) := by
  simp [observationalDistance, observationalDepth_of_ne D hxy]

theorem observationalDistance_eq_zero_iff
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    observationalDistance D x y = .zero ↔ x = y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [observationalDistance]
  · simp [observationalDistance, observationalDepth,
      SeparationDistance.ofDepth, hxy]

theorem observationalDistance_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    observationalDistance D x y =
      observationalDistance D y x := by
  unfold observationalDistance
  rw [observationalDepth_symm D x y]

/-- Strong ultrametric inequality in the symbolic distance scale. -/
theorem observationalDistance_strong_triangle
    (D : PartialAlg.{u,v} Sigma)
    (x y z : Free.GeneratedAns D) :
    SeparationDistance.le
      (observationalDistance D x z)
      (SeparationDistance.max
        (observationalDistance D x y)
        (observationalDistance D y z)) := by
  apply SeparationDistance.ofDepth_strong_triangle
  exact observationalDepth_min_triangle D x y z

/-- Abstract ultrametric space over the discrete symbolic separation scale. -/
structure DiscreteUltrametric (X : Type w) where
  distance : X → X → SeparationDistance
  eq_zero : ∀ x y, distance x y = .zero ↔ x = y
  symm : ∀ x y, distance x y = distance y x
  strong_triangle : ∀ x y z,
    SeparationDistance.le
      (distance x z)
      (SeparationDistance.max (distance x y) (distance y z))

/-- Generated Answers with finite-tag semantics carry a canonical discrete
    ultrametric. -/
noncomputable def finiteTagDiscreteUltrametric
    (D : PartialAlg.{u,v} Sigma) :
    DiscreteUltrametric (Free.GeneratedAns D) where
  distance := observationalDistance D
  eq_zero := observationalDistance_eq_zero_iff D
  symm := observationalDistance_symm D
  strong_triangle := observationalDistance_strong_triangle D
/-- The finite observational ball of stage `n` around `x`. Membership means
    that every preserving model with exactly `n` finite tags identifies the
    center and the point. -/
def FiniteObservationBall
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) : Prop :=
  FiniteTagEqAt D n x y

/-- Closed ball for the symbolic observational distance. -/
def ObservationalClosedBall
    (D : PartialAlg.{u,v} Sigma) (r : SeparationDistance)
    (x y : Free.GeneratedAns D) : Prop :=
  SeparationDistance.le (observationalDistance D x y) r

@[simp] theorem finiteObservationBall_center
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x : Free.GeneratedAns D) :
    FiniteObservationBall D n x x :=
  finiteTagEqAt_refl D n x

/-- Stage `n` is exactly the closed ultrametric ball of symbolic radius
    `level (n + 1)`. The successor shift records that stage `n` still
    identifies pairs whose separation rank is strictly larger than `n`. -/
theorem finiteObservationBall_iff_closedBall_level_succ
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) :
    FiniteObservationBall D n x y ↔
      ObservationalClosedBall D (.level (Nat.succ n)) x y := by
  unfold FiniteObservationBall ObservationalClosedBall
  classical
  by_cases hxy : x = y
  · subst y
    rw [observationalDistance_self]
    constructor
    · intro h
      exact SeparationDistance.le_zero _
    · intro h
      exact finiteTagEqAt_refl D n x
  · rw [observationalDistance_of_ne D hxy]
    change FiniteTagEqAt D n x y ↔
      Nat.succ n ≤ finiteSeparationRank D x y
    rw [finiteTagEqAt_iff_lt_rank D hxy n]
    rfl

/-- Uniform rank description of ball membership. -/
theorem finiteObservationBall_iff_eq_or_lt_rank
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) :
    FiniteObservationBall D n x y ↔
      x = y ∨ n < finiteSeparationRank D x y :=
  finiteTagEqAt_iff_eq_or_lt_rank D n x y

/-- Balls shrink as the finite observation budget grows. -/
theorem finiteObservationBall_antitone
    (D : PartialAlg.{u,v} Sigma)
    {n m : Nat} (hnm : n ≤ m)
    (x : Free.GeneratedAns D) :
    ∀ y : Free.GeneratedAns D,
      FiniteObservationBall D m x y →
        FiniteObservationBall D n x y := by
  intro y hxy
  exact finiteTagEqAt_antitone D hnm hxy

/-- Any two points of one stage ball are equivalent at that stage. -/
theorem finiteObservationBall_pairwise
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {center x y : Free.GeneratedAns D}
    (hx : FiniteObservationBall D n center x)
    (hy : FiniteObservationBall D n center y) :
    FiniteObservationBall D n x y :=
  finiteTagEqAt_trans D n
    (finiteTagEqAt_symm D n hx) hy

/-- Every point of a ball may serve as its center. -/
theorem finiteObservationBall_change_center
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y : Free.GeneratedAns D}
    (hxy : FiniteObservationBall D n x y) :
    ∀ z : Free.GeneratedAns D,
      FiniteObservationBall D n x z ↔
        FiniteObservationBall D n y z := by
  intro z
  exact finiteTagEqAt_left_congr D n hxy

/-- Two same-stage balls with a common point are equal as predicates. -/
theorem finiteObservationBall_same_stage_eq_of_common_point
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y w : Free.GeneratedAns D}
    (hxw : FiniteObservationBall D n x w)
    (hyw : FiniteObservationBall D n y w) :
    ∀ z : Free.GeneratedAns D,
      FiniteObservationBall D n x z ↔
        FiniteObservationBall D n y z := by
  exact
    (finiteTagEqAt_classes_coincide_of_common_point
      D n hxw hyw).2

/-- Predicate-level disjointness of two finite observational balls. -/
def FiniteObservationBallDisjoint
    (D : PartialAlg.{u,v} Sigma)
    (n m : Nat) (x y : Free.GeneratedAns D) : Prop :=
  ∀ z : Free.GeneratedAns D,
    ¬ (FiniteObservationBall D n x z ∧
      FiniteObservationBall D m y z)

/-- Same-stage ultrametric balls are equal or disjoint. -/
theorem finiteObservationBall_equal_or_disjoint
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) :
    (∀ z : Free.GeneratedAns D,
      FiniteObservationBall D n x z ↔
        FiniteObservationBall D n y z) ∨
      FiniteObservationBallDisjoint D n n x y := by
  classical
  by_cases hxy : FiniteObservationBall D n x y
  · exact Or.inl (finiteObservationBall_change_center D n hxy)
  · apply Or.inr
    intro z hz
    apply hxy
    exact finiteTagEqAt_trans D n hz.1
      (finiteTagEqAt_symm D n hz.2)

/-- Predicate-level inclusion of finite observational balls. -/
def FiniteObservationBallIncluded
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat) (x : Free.GeneratedAns D)
    (m : Nat) (y : Free.GeneratedAns D) : Prop :=
  ∀ z : Free.GeneratedAns D,
    FiniteObservationBall D n x z →
      FiniteObservationBall D m y z

/-- Arbitrary observational balls satisfy the characteristic ultrametric
    trichotomy: the first is contained in the second, the second is contained
    in the first, or the two are disjoint. -/
theorem finiteObservationBall_nested_or_disjoint
    (D : PartialAlg.{u,v} Sigma)
    (n m : Nat) (x y : Free.GeneratedAns D) :
    FiniteObservationBallIncluded D n x m y ∨
      FiniteObservationBallIncluded D m y n x ∨
        FiniteObservationBallDisjoint D n m x y := by
  classical
  rcases Nat.le_total n m with hnm | hmn
  · by_cases hmeet :
        ∃ w : Free.GeneratedAns D,
          FiniteObservationBall D n x w ∧
            FiniteObservationBall D m y w
    · rcases hmeet with ⟨w, hxw, hyw⟩
      apply Or.inr
      apply Or.inl
      intro z hyz
      have hwzM : FiniteObservationBall D m w z :=
        finiteTagEqAt_trans D m
          (finiteTagEqAt_symm D m hyw) hyz
      have hwzN : FiniteObservationBall D n w z :=
        finiteTagEqAt_antitone D hnm hwzM
      exact finiteTagEqAt_trans D n hxw hwzN
    · apply Or.inr
      apply Or.inr
      intro z hz
      exact hmeet ⟨z, hz.1, hz.2⟩
  · by_cases hmeet :
        ∃ w : Free.GeneratedAns D,
          FiniteObservationBall D n x w ∧
            FiniteObservationBall D m y w
    · rcases hmeet with ⟨w, hxw, hyw⟩
      apply Or.inl
      intro z hxz
      have hwzN : FiniteObservationBall D n w z :=
        finiteTagEqAt_trans D n
          (finiteTagEqAt_symm D n hxw) hxz
      have hwzM : FiniteObservationBall D m w z :=
        finiteTagEqAt_antitone D hmn hwzN
      exact finiteTagEqAt_trans D m hyw hwzM
    · apply Or.inr
      apply Or.inr
      intro z hz
      exact hmeet ⟨z, hz.1, hz.2⟩

/-- A distinct point belongs to the stage-`n` ball exactly before the stage
    reaches its finite separation rank. -/
theorem finiteObservationBall_of_lt_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hn : n < finiteSeparationRank D x y) :
    FiniteObservationBall D n x y :=
  finiteTagEqAt_of_lt_rank D hxy hn

/-- At the separation rank itself, the point has left the ball. -/
theorem not_finiteObservationBall_at_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y) :
    ¬ FiniteObservationBall D
      (finiteSeparationRank D x y) x y :=
  not_finiteTagEqAt_at_rank D hxy

/-- Exact successor boundary for a pair whose rank is `n + 1`. -/
theorem finiteObservationBall_rank_boundary
    (D : PartialAlg.{u,v} Sigma)
    {x y : Free.GeneratedAns D} (hxy : x ≠ y)
    {n : Nat} (hrank : finiteSeparationRank D x y = Nat.succ n) :
    FiniteObservationBall D n x y ∧
      ¬ FiniteObservationBall D (Nat.succ n) x y :=
  finiteTagEqAt_rank_boundary D hxy hrank
/-- A predicate is observationally open when every one of its points contains
    some finite observational ball that remains inside the predicate. -/
def ObservationalOpen
    (D : PartialAlg.{u,v} Sigma)
    (U : Free.GeneratedAns D → Prop) : Prop :=
  ∀ x : Free.GeneratedAns D, U x →
    ∃ n : Nat, ∀ y : Free.GeneratedAns D,
      FiniteObservationBall D n x y → U y

/-- Observational closedness is openness of the complement. -/
def ObservationalClosed
    (D : PartialAlg.{u,v} Sigma)
    (U : Free.GeneratedAns D → Prop) : Prop :=
  ObservationalOpen D (fun x => ¬ U x)

theorem observationalOpen_empty
    (D : PartialAlg.{u,v} Sigma) :
    ObservationalOpen D (fun _ => False) := by
  intro x hx
  exact False.elim hx

theorem observationalOpen_univ
    (D : PartialAlg.{u,v} Sigma) :
    ObservationalOpen D (fun _ => True) := by
  intro x hx
  exact ⟨0, fun y hxy => True.intro⟩

theorem observationalOpen_union
    (D : PartialAlg.{u,v} Sigma)
    {U V : Free.GeneratedAns D → Prop}
    (hU : ObservationalOpen D U)
    (hV : ObservationalOpen D V) :
    ObservationalOpen D (fun x => U x ∨ V x) := by
  intro x hx
  cases hx with
  | inl hxU =>
      rcases hU x hxU with ⟨n, hn⟩
      exact ⟨n, fun y hxy => Or.inl (hn y hxy)⟩
  | inr hxV =>
      rcases hV x hxV with ⟨n, hn⟩
      exact ⟨n, fun y hxy => Or.inr (hn y hxy)⟩

theorem observationalOpen_iUnion
    (D : PartialAlg.{u,v} Sigma)
    {I : Type w} (U : I → Free.GeneratedAns D → Prop)
    (hU : ∀ i : I, ObservationalOpen D (U i)) :
    ObservationalOpen D (fun x => ∃ i : I, U i x) := by
  intro x hx
  rcases hx with ⟨i, hix⟩
  rcases hU i x hix with ⟨n, hn⟩
  exact ⟨n, fun y hxy => ⟨i, hn y hxy⟩⟩

theorem observationalOpen_inter
    (D : PartialAlg.{u,v} Sigma)
    {U V : Free.GeneratedAns D → Prop}
    (hU : ObservationalOpen D U)
    (hV : ObservationalOpen D V) :
    ObservationalOpen D (fun x => U x ∧ V x) := by
  intro x hx
  rcases hU x hx.1 with ⟨n, hn⟩
  rcases hV x hx.2 with ⟨m, hm⟩
  refine ⟨Nat.max n m, ?_⟩
  intro y hxy
  constructor
  · apply hn y
    exact finiteObservationBall_antitone D
      (Nat.le_max_left n m) x y hxy
  · apply hm y
    exact finiteObservationBall_antitone D
      (Nat.le_max_right n m) x y hxy

/-- Every finite observational ball is open. -/
theorem observationalOpen_ball
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (center : Free.GeneratedAns D) :
    ObservationalOpen D
      (fun x => FiniteObservationBall D n center x) := by
  intro x hx
  refine ⟨n, ?_⟩
  intro y hxy
  exact finiteTagEqAt_trans D n hx hxy

/-- The complement of every finite observational ball is open. -/
theorem observationalOpen_compl_ball
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (center : Free.GeneratedAns D) :
    ObservationalOpen D
      (fun x => ¬ FiniteObservationBall D n center x) := by
  intro x hx
  refine ⟨n, ?_⟩
  intro y hxy hy
  apply hx
  exact finiteTagEqAt_trans D n hy
    (finiteTagEqAt_symm D n hxy)

/-- A minimal predicate-level topology interface, sufficient for the finite
    observational topology without importing a separate topology library. -/
structure PredicateTopology (X : Type w) where
  IsOpen : (X → Prop) → Prop
  empty_open : IsOpen (fun _ => False)
  univ_open : IsOpen (fun _ => True)
  inter_open : ∀ U V : X → Prop,
    IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
  iUnion_open : ∀ (I : Type w) (U : I → X → Prop),
    (∀ i : I, IsOpen (U i)) →
      IsOpen (fun x => ∃ i : I, U i x)

/-- The topology generated by finite observational balls. -/
def finiteObservationTopology
    (D : PartialAlg.{u,v} Sigma) :
    PredicateTopology (Free.GeneratedAns D) where
  IsOpen := ObservationalOpen D
  empty_open := observationalOpen_empty D
  univ_open := observationalOpen_univ D
  inter_open := by
    intro U V hU hV
    exact observationalOpen_inter D hU hV
  iUnion_open := by
    intro I U hU
    exact observationalOpen_iUnion D U hU

/-- Predicate-level clopenness. -/
def PredicateClopen {X : Type w}
    (T : PredicateTopology X) (U : X → Prop) : Prop :=
  T.IsOpen U ∧ T.IsOpen (fun x => ¬ U x)

/-- Every finite observational ball is clopen. -/
theorem finiteObservationBall_clopen
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (center : Free.GeneratedAns D) :
    PredicateClopen (finiteObservationTopology D)
      (fun x => FiniteObservationBall D n center x) := by
  exact ⟨observationalOpen_ball D n center,
    observationalOpen_compl_ball D n center⟩

/-- Predicate-level disjointness for arbitrary neighborhoods. -/
def PredicateDisjoint {X : Type w}
    (U V : X → Prop) : Prop :=
  ∀ x : X, ¬ (U x ∧ V x)

/-- Hausdorff separation for a predicate topology. -/
def PredicateHausdorff {X : Type w}
    (T : PredicateTopology X) : Prop :=
  ∀ x y : X, x ≠ y →
    ∃ U V : X → Prop,
      T.IsOpen U ∧ T.IsOpen V ∧
        U x ∧ V y ∧ PredicateDisjoint U V

/-- Distinct generated Answers admit disjoint finite observational ball
    neighborhoods at their separation rank. -/
theorem finiteObservationTopology_hausdorff
    (D : PartialAlg.{u,v} Sigma) :
    PredicateHausdorff (finiteObservationTopology D) := by
  intro x y hxy
  let n := finiteSeparationRank D x y
  refine ⟨fun z => FiniteObservationBall D n x z,
    fun z => FiniteObservationBall D n y z, ?_, ?_, ?_, ?_, ?_⟩
  · exact observationalOpen_ball D n x
  · exact observationalOpen_ball D n y
  · exact finiteObservationBall_center D n x
  · exact finiteObservationBall_center D n y
  · intro z hz
    apply not_finiteObservationBall_at_rank D hxy
    exact finiteTagEqAt_trans D n hz.1
      (finiteTagEqAt_symm D n hz.2)

/-- Zero-dimensionality expressed by a clopen neighborhood basis. -/
def PredicateZeroDimensional {X : Type w}
    (T : PredicateTopology X) : Prop :=
  ∀ U : X → Prop, T.IsOpen U →
    ∀ x : X, U x →
      ∃ B : X → Prop,
        PredicateClopen T B ∧ B x ∧
          ∀ y : X, B y → U y

/-- The finite observational topology is zero-dimensional: every open
    neighborhood contains a clopen finite observational ball. -/
theorem finiteObservationTopology_zeroDimensional
    (D : PartialAlg.{u,v} Sigma) :
    PredicateZeroDimensional (finiteObservationTopology D) := by
  intro U hU x hx
  change ObservationalOpen D U at hU
  rcases hU x hx with ⟨n, hn⟩
  refine ⟨fun y => FiniteObservationBall D n x y, ?_, ?_, ?_⟩
  · exact finiteObservationBall_clopen D n x
  · exact finiteObservationBall_center D n x
  · intro y hxy
    exact hn y hxy

/-- Singletons are observationally closed. -/
theorem observationalClosed_singleton
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    ObservationalClosed D (fun y => y = x) := by
  intro y hy
  refine ⟨finiteSeparationRank D y x, ?_⟩
  intro z hyz hzx
  subst z
  exact (not_finiteObservationBall_at_rank D hy) hyz

/-- The intersection of all finite observational balls around a point is the
    singleton consisting of that point. -/
theorem all_finiteObservationBalls_iff_eq
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    (∀ n : Nat, FiniteObservationBall D n x y) ↔ x = y :=
  forall_finiteTagEqAt_iff_eq D x y
/-- A sequence converges observationally to `x` when it is eventually inside
    every finite observational ball around `x`. -/
def ObservationalConverges
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ k : Nat, N ≤ k →
      FiniteObservationBall D n x (s k)

/-- A sequence is observationally Cauchy when, at every finite stage, all
    sufficiently late terms lie in one observational equivalence class. -/
def ObservationalCauchy
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ i j : Nat, N ≤ i → N ≤ j →
      FiniteObservationBall D n (s i) (s j)

/-- Pointwise equality from some index onward. -/
def EventuallyPointwiseEqual {X : Type w}
    (s t : Nat → X) : Prop :=
  ∃ N : Nat, ∀ k : Nat, N ≤ k → s k = t k

@[refl] theorem eventuallyPointwiseEqual_refl {X : Type w}
    (s : Nat → X) : EventuallyPointwiseEqual s s := by
  exact ⟨0, fun k hk => rfl⟩

@[symm] theorem eventuallyPointwiseEqual_symm {X : Type w}
    {s t : Nat → X} :
    EventuallyPointwiseEqual s t →
      EventuallyPointwiseEqual t s := by
  rintro ⟨N, hN⟩
  exact ⟨N, fun k hk => Eq.symm (hN k hk)⟩

theorem eventuallyPointwiseEqual_trans {X : Type w}
    {r s t : Nat → X} :
    EventuallyPointwiseEqual r s →
      EventuallyPointwiseEqual s t →
        EventuallyPointwiseEqual r t := by
  rintro ⟨Nr, hr⟩ ⟨Ns, hs⟩
  refine ⟨Nat.max Nr Ns, ?_⟩
  intro k hk
  exact Eq.trans
    (hr k (Nat.le_trans (Nat.le_max_left Nr Ns) hk))
    (hs k (Nat.le_trans (Nat.le_max_right Nr Ns) hk))

/-- Constant sequences converge to their constant value. -/
theorem observationalConverges_const
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    ObservationalConverges D (fun _ => x) x := by
  intro n
  exact ⟨0, fun k hk => finiteObservationBall_center D n x⟩

/-- Constant sequences are Cauchy. -/
theorem observationalCauchy_const
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    ObservationalCauchy D (fun _ => x) := by
  intro n
  exact ⟨0, fun i j hi hj => finiteObservationBall_center D n x⟩

/-- Every convergent sequence is Cauchy. -/
theorem observationalConverges_implies_cauchy
    (D : PartialAlg.{u,v} Sigma)
    {s : Nat → Free.GeneratedAns D}
    {x : Free.GeneratedAns D}
    (hs : ObservationalConverges D s x) :
    ObservationalCauchy D s := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact finiteObservationBall_pairwise D n
    (hN i hi) (hN j hj)

/-- Observational limits are unique. -/
theorem observationalConverges_unique
    (D : PartialAlg.{u,v} Sigma)
    {s : Nat → Free.GeneratedAns D}
    {x y : Free.GeneratedAns D}
    (hx : ObservationalConverges D s x)
    (hy : ObservationalConverges D s y) :
    x = y := by
  apply (all_finiteObservationBalls_iff_eq D x y).1
  intro n
  rcases hx n with ⟨Nx, hxN⟩
  rcases hy n with ⟨Ny, hyN⟩
  have hxk := hxN (Nat.max Nx Ny) (Nat.le_max_left Nx Ny)
  have hyk := hyN (Nat.max Nx Ny) (Nat.le_max_right Nx Ny)
  exact finiteTagEqAt_trans D n hxk
    (finiteTagEqAt_symm D n hyk)

/-- Eventual pointwise equality preserves convergence. -/
theorem observationalConverges_of_eventuallyPointwiseEqual
    (D : PartialAlg.{u,v} Sigma)
    {s t : Nat → Free.GeneratedAns D}
    {x : Free.GeneratedAns D}
    (hst : EventuallyPointwiseEqual s t)
    (hs : ObservationalConverges D s x) :
    ObservationalConverges D t x := by
  rcases hst with ⟨Ne, he⟩
  intro n
  rcases hs n with ⟨Ns, hsN⟩
  refine ⟨Nat.max Ns Ne, ?_⟩
  intro k hk
  have hsk : Ns ≤ k :=
    Nat.le_trans (Nat.le_max_left Ns Ne) hk
  have hek : s k = t k :=
    he k (Nat.le_trans (Nat.le_max_right Ns Ne) hk)
  rw [← hek]
  exact hsN k hsk

theorem observationalConverges_congr_eventuallyPointwiseEqual
    (D : PartialAlg.{u,v} Sigma)
    {s t : Nat → Free.GeneratedAns D}
    (hst : EventuallyPointwiseEqual s t)
    (x : Free.GeneratedAns D) :
    ObservationalConverges D s x ↔
      ObservationalConverges D t x := by
  constructor
  · exact observationalConverges_of_eventuallyPointwiseEqual D hst
  · exact observationalConverges_of_eventuallyPointwiseEqual D
      (eventuallyPointwiseEqual_symm hst)

/-- Eventual pointwise equality also preserves the Cauchy property. -/
theorem observationalCauchy_of_eventuallyPointwiseEqual
    (D : PartialAlg.{u,v} Sigma)
    {s t : Nat → Free.GeneratedAns D}
    (hst : EventuallyPointwiseEqual s t)
    (hs : ObservationalCauchy D s) :
    ObservationalCauchy D t := by
  rcases hst with ⟨Ne, he⟩
  intro n
  rcases hs n with ⟨Ns, hsN⟩
  refine ⟨Nat.max Ns Ne, ?_⟩
  intro i j hi hj
  have his : Ns ≤ i :=
    Nat.le_trans (Nat.le_max_left Ns Ne) hi
  have hjs : Ns ≤ j :=
    Nat.le_trans (Nat.le_max_left Ns Ne) hj
  have hei : s i = t i :=
    he i (Nat.le_trans (Nat.le_max_right Ns Ne) hi)
  have hej : s j = t j :=
    he j (Nat.le_trans (Nat.le_max_right Ns Ne) hj)
  rw [← hei, ← hej]
  exact hsN i j his hjs

theorem observationalCauchy_congr_eventuallyPointwiseEqual
    (D : PartialAlg.{u,v} Sigma)
    {s t : Nat → Free.GeneratedAns D}
    (hst : EventuallyPointwiseEqual s t) :
    ObservationalCauchy D s ↔ ObservationalCauchy D t := by
  constructor
  · exact observationalCauchy_of_eventuallyPointwiseEqual D hst
  · exact observationalCauchy_of_eventuallyPointwiseEqual D
      (eventuallyPointwiseEqual_symm hst)

/-- Every eventually constant sequence converges to its eventual value. -/
theorem observationalConverges_of_eventually_constant
    (D : PartialAlg.{u,v} Sigma)
    {s : Nat → Free.GeneratedAns D}
    {x : Free.GeneratedAns D}
    (hs : ∃ N : Nat, ∀ k : Nat, N ≤ k → s k = x) :
    ObservationalConverges D s x := by
  rcases hs with ⟨N, hN⟩
  intro n
  refine ⟨N, ?_⟩
  intro k hk
  rw [hN k hk]
  exact finiteObservationBall_center D n x

/-- Ball convergence agrees exactly with convergence in every observationally
    open neighborhood. -/
theorem observationalConverges_iff_open_neighborhoods
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    ObservationalConverges D s x ↔
      ∀ U : Free.GeneratedAns D → Prop,
        ObservationalOpen D U → U x →
          ∃ N : Nat, ∀ k : Nat, N ≤ k → U (s k) := by
  constructor
  · intro hs U hU hx
    rcases hU x hx with ⟨n, hn⟩
    rcases hs n with ⟨N, hN⟩
    exact ⟨N, fun k hk => hn (s k) (hN k hk)⟩
  · intro hs n
    exact hs
      (fun y => FiniteObservationBall D n x y)
      (observationalOpen_ball D n x)
      (finiteObservationBall_center D n x)

/-- Rank formulation of convergence: for every finite stage, late terms are
    either equal to the limit or have separation rank beyond that stage. -/
theorem observationalConverges_iff_rank_tends_to_infinity
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    ObservationalConverges D s x ↔
      ∀ n : Nat, ∃ N : Nat,
        ∀ k : Nat, N ≤ k →
          x = s k ∨ n < finiteSeparationRank D x (s k) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (finiteObservationBall_iff_eq_or_lt_rank
      D n x (s k)).1 (hN k hk)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (finiteObservationBall_iff_eq_or_lt_rank
      D n x (s k)).2 (hN k hk)

/-- Distance formulation of convergence: late terms lie in every symbolic
    closed ball `level (n + 1)` around the limit. -/
theorem observationalConverges_iff_distance_tends_to_zero
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    ObservationalConverges D s x ↔
      ∀ n : Nat, ∃ N : Nat,
        ∀ k : Nat, N ≤ k →
          ObservationalClosedBall D (.level (Nat.succ n)) x (s k) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (finiteObservationBall_iff_closedBall_level_succ
      D n x (s k)).1 (hN k hk)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (finiteObservationBall_iff_closedBall_level_succ
      D n x (s k)).2 (hN k hk)

/-- Rank formulation of the Cauchy property. -/
theorem observationalCauchy_iff_pairwise_rank_tends_to_infinity
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D) :
    ObservationalCauchy D s ↔
      ∀ n : Nat, ∃ N : Nat,
        ∀ i j : Nat, N ≤ i → N ≤ j →
          s i = s j ∨ n < finiteSeparationRank D (s i) (s j) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro i j hi hj
    exact (finiteObservationBall_iff_eq_or_lt_rank
      D n (s i) (s j)).1 (hN i j hi hj)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro i j hi hj
    exact (finiteObservationBall_iff_eq_or_lt_rank
      D n (s i) (s j)).2 (hN i j hi hj)

/-- Completeness is deliberately isolated as an additional property; none of
    the preceding sequence theory assumes it. -/
def ObservationalComplete
    (D : PartialAlg.{u,v} Sigma) : Prop :=
  ∀ s : Nat → Free.GeneratedAns D,
    ObservationalCauchy D s →
      ∃ x : Free.GeneratedAns D, ObservationalConverges D s x
/-- Two sequences are asymptotically observationally equivalent when, at every
    finite stage, their terms are eventually indistinguishable pointwise. -/
def ObservationalSequenceEq
    (D : PartialAlg.{u,v} Sigma)
    (s t : Nat → Free.GeneratedAns D) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ k : Nat, N ≤ k →
      FiniteObservationBall D n (s k) (t k)

@[refl] theorem observationalSequenceEq_refl
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D) :
    ObservationalSequenceEq D s s := by
  intro n
  exact ⟨0, fun k hk => finiteObservationBall_center D n (s k)⟩

@[symm] theorem observationalSequenceEq_symm
    (D : PartialAlg.{u,v} Sigma)
    {s t : Nat → Free.GeneratedAns D} :
    ObservationalSequenceEq D s t →
      ObservationalSequenceEq D t s := by
  intro hst n
  rcases hst n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact finiteTagEqAt_symm D n (hN k hk)

theorem observationalSequenceEq_trans
    (D : PartialAlg.{u,v} Sigma)
    {r s t : Nat → Free.GeneratedAns D} :
    ObservationalSequenceEq D r s →
      ObservationalSequenceEq D s t →
        ObservationalSequenceEq D r t := by
  intro hrs hst n
  rcases hrs n with ⟨Nr, hr⟩
  rcases hst n with ⟨Ns, hs⟩
  refine ⟨Nat.max Nr Ns, ?_⟩
  intro k hk
  exact finiteTagEqAt_trans D n
    (hr k (Nat.le_trans (Nat.le_max_left Nr Ns) hk))
    (hs k (Nat.le_trans (Nat.le_max_right Nr Ns) hk))

/-- Convergence to `x` is exactly asymptotic equivalence with the constant
    sequence at `x`. -/
theorem observationalConverges_iff_sequenceEq_const
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    ObservationalConverges D s x ↔
      ObservationalSequenceEq D s (fun _ => x) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact finiteTagEqAt_symm D n (hN k hk)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact finiteTagEqAt_symm D n (hN k hk)

/-- Cauchy sequences are packaged as the raw representatives of the
    observational completion. -/
structure ObservationalCauchySeq
    (D : PartialAlg.{u,v} Sigma) where
  term : Nat → Free.GeneratedAns D
  cauchy : ObservationalCauchy D term

/-- Asymptotic observational equivalence is a setoid on Cauchy sequences. -/
def observationalCauchySetoid
    (D : PartialAlg.{u,v} Sigma) :
    Setoid (ObservationalCauchySeq D) where
  r a b := ObservationalSequenceEq D a.term b.term
  iseqv := by
    constructor
    · intro a
      exact observationalSequenceEq_refl D a.term
    · intro a b hab
      exact observationalSequenceEq_symm D hab
    · intro a b c hab hbc
      exact observationalSequenceEq_trans D hab hbc

/-- The observational completion is the quotient of Cauchy sequences by
    asymptotic finite-stage agreement. -/
def ObservationalCompletion
    (D : PartialAlg.{u,v} Sigma) :=
  Quotient (observationalCauchySetoid D)

/-- Constant Cauchy representative of a generated Answer. -/
def constantObservationalCauchySeq
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    ObservationalCauchySeq D where
  term := fun _ => x
  cauchy := observationalCauchy_const D x

/-- Canonical class of a Cauchy representative. -/
def observationalCompletionClass
    (D : PartialAlg.{u,v} Sigma)
    (s : ObservationalCauchySeq D) :
    ObservationalCompletion D :=
  Quotient.mk (observationalCauchySetoid D) s

/-- Canonical embedding of generated Answers into their observational
    completion. -/
def observationalCompletionEmbed
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    ObservationalCompletion D :=
  observationalCompletionClass D
    (constantObservationalCauchySeq D x)

/-- Equality of represented completion points is exactly asymptotic
    observational equivalence of representatives. -/
theorem observationalCompletionClass_eq_iff
    (D : PartialAlg.{u,v} Sigma)
    (s t : ObservationalCauchySeq D) :
    observationalCompletionClass D s =
        observationalCompletionClass D t ↔
      ObservationalSequenceEq D s.term t.term := by
  constructor
  · intro h
    have hrel := Quotient.exact h
    exact hrel
  · intro h
    exact Quotient.sound h

/-- The canonical embedding is injective because finite observations are
    Hausdorff. -/
theorem observationalCompletionEmbed_injective
    (D : PartialAlg.{u,v} Sigma) :
    Function.Injective (observationalCompletionEmbed D) := by
  intro x y hxy
  have hrel :
      ObservationalSequenceEq D (fun _ => x) (fun _ => y) := by
    have hq := Quotient.exact hxy
    exact hq
  apply (all_finiteObservationBalls_iff_eq D x y).1
  intro n
  rcases hrel n with ⟨N, hN⟩
  exact hN N (Nat.le_refl N)

/-- A Cauchy representative defines the embedded point `x` exactly when that
    representative converges to `x`. -/
theorem observationalCompletionClass_eq_embed_iff
    (D : PartialAlg.{u,v} Sigma)
    (s : ObservationalCauchySeq D)
    (x : Free.GeneratedAns D) :
    observationalCompletionClass D s =
        observationalCompletionEmbed D x ↔
      ObservationalConverges D s.term x := by
  change observationalCompletionClass D s =
      observationalCompletionClass D
        (constantObservationalCauchySeq D x) ↔
    ObservationalConverges D s.term x
  rw [observationalCompletionClass_eq_iff]
  simpa [constantObservationalCauchySeq] using
    (observationalConverges_iff_sequenceEq_const D s.term x).symm

/-- The completion embedding identifies an original Answer with a represented
    Cauchy class precisely when that class converges to the Answer. -/
theorem observationalCompletionEmbed_eq_class_iff
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D)
    (s : ObservationalCauchySeq D) :
    observationalCompletionEmbed D x =
        observationalCompletionClass D s ↔
      ObservationalConverges D s.term x := by
  constructor
  · intro h
    exact (observationalCompletionClass_eq_embed_iff D s x).1 h.symm
  · intro h
    exact ((observationalCompletionClass_eq_embed_iff D s x).2 h).symm
/-- Eventual indistinguishability of two sequences at one fixed finite stage. -/
def ObservationalSequenceEqAt
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (s t : Nat → Free.GeneratedAns D) : Prop :=
  ∃ N : Nat, ∀ k : Nat, N ≤ k →
    FiniteObservationBall D n (s k) (t k)

@[refl] theorem observationalSequenceEqAt_refl
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (s : Nat → Free.GeneratedAns D) :
    ObservationalSequenceEqAt D n s s := by
  exact ⟨0, fun k hk => finiteObservationBall_center D n (s k)⟩

@[symm] theorem observationalSequenceEqAt_symm
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {s t : Nat → Free.GeneratedAns D} :
    ObservationalSequenceEqAt D n s t →
      ObservationalSequenceEqAt D n t s := by
  rintro ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact finiteTagEqAt_symm D n (hN k hk)

theorem observationalSequenceEqAt_trans
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {r s t : Nat → Free.GeneratedAns D} :
    ObservationalSequenceEqAt D n r s →
      ObservationalSequenceEqAt D n s t →
        ObservationalSequenceEqAt D n r t := by
  rintro ⟨Nr, hr⟩ ⟨Ns, hs⟩
  refine ⟨Nat.max Nr Ns, ?_⟩
  intro k hk
  exact finiteTagEqAt_trans D n
    (hr k (Nat.le_trans (Nat.le_max_left Nr Ns) hk))
    (hs k (Nat.le_trans (Nat.le_max_right Nr Ns) hk))

/-- Full asymptotic equivalence is the intersection of all fixed-stage
    eventual equivalences. -/
theorem observationalSequenceEq_iff_forall_eqAt
    (D : PartialAlg.{u,v} Sigma)
    (s t : Nat → Free.GeneratedAns D) :
    ObservationalSequenceEq D s t ↔
      ∀ n : Nat, ObservationalSequenceEqAt D n s t := by
  rfl

/-- Eventual equivalence at a larger observational budget implies eventual
    equivalence at every smaller budget. -/
theorem observationalSequenceEqAt_antitone
    (D : PartialAlg.{u,v} Sigma)
    {n m : Nat} (hnm : n ≤ m)
    {s t : Nat → Free.GeneratedAns D} :
    ObservationalSequenceEqAt D m s t →
      ObservationalSequenceEqAt D n s t := by
  rintro ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact finiteTagEqAt_antitone D hnm (hN k hk)

/-- Fixed-stage eventual agreement is invariant under replacing either
    sequence by an asymptotically equivalent representative. -/
theorem observationalSequenceEqAt_congr
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {s s' t t' : Nat → Free.GeneratedAns D}
    (hss : ObservationalSequenceEq D s s')
    (htt : ObservationalSequenceEq D t t') :
    ObservationalSequenceEqAt D n s t ↔
      ObservationalSequenceEqAt D n s' t' := by
  have hssn : ObservationalSequenceEqAt D n s s' := hss n
  have httn : ObservationalSequenceEqAt D n t t' := htt n
  constructor
  · intro hst
    exact observationalSequenceEqAt_trans D n
      (observationalSequenceEqAt_symm D n hssn)
      (observationalSequenceEqAt_trans D n hst httn)
  · intro hst
    exact observationalSequenceEqAt_trans D n hssn
      (observationalSequenceEqAt_trans D n hst
        (observationalSequenceEqAt_symm D n httn))

/-- Finite-stage indistinguishability descends to the observational
    completion. -/
def CompletionEqAt
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : ObservationalCompletion D) : Prop :=
  Quotient.liftOn₂ x y
    (fun s t => ObservationalSequenceEqAt D n s.term t.term)
    (by
      intro a b a' b' haa hbb
      change ObservationalSequenceEq D a.term a'.term at haa
      change ObservationalSequenceEq D b.term b'.term at hbb
      apply propext
      exact observationalSequenceEqAt_congr D n haa hbb)

@[refl] theorem completionEqAt_refl
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x : ObservationalCompletion D) :
    CompletionEqAt D n x x := by
  refine Quotient.inductionOn x ?_
  intro s
  exact observationalSequenceEqAt_refl D n s.term

@[symm] theorem completionEqAt_symm
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y : ObservationalCompletion D} :
    CompletionEqAt D n x y →
      CompletionEqAt D n y x := by
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  exact observationalSequenceEqAt_symm D n hst

theorem completionEqAt_trans
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    {x y z : ObservationalCompletion D} :
    CompletionEqAt D n x y →
      CompletionEqAt D n y z →
        CompletionEqAt D n x z := by
  refine Quotient.inductionOn x ?_
  intro r
  refine Quotient.inductionOn y ?_
  intro s
  refine Quotient.inductionOn z ?_
  intro t hrs hst
  exact observationalSequenceEqAt_trans D n hrs hst

/-- The completion retains the descending finite observational filtration. -/
theorem completionEqAt_antitone
    (D : PartialAlg.{u,v} Sigma)
    {n m : Nat} (hnm : n ≤ m)
    {x y : ObservationalCompletion D} :
    CompletionEqAt D m x y →
      CompletionEqAt D n x y := by
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  exact observationalSequenceEqAt_antitone D hnm hst

/-- The completion embedding preserves every finite observational stage. -/
theorem completionEqAt_embed_iff
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (x y : Free.GeneratedAns D) :
    CompletionEqAt D n
        (observationalCompletionEmbed D x)
        (observationalCompletionEmbed D y) ↔
      FiniteObservationBall D n x y := by
  change ObservationalSequenceEqAt D n
      (fun _ => x) (fun _ => y) ↔
    FiniteObservationBall D n x y
  constructor
  · rintro ⟨N, hN⟩
    exact hN N (Nat.le_refl N)
  · intro hxy
    exact ⟨0, fun k hk => hxy⟩

/-- Completion points are equal exactly when they agree at every finite
    observational stage. -/
theorem forall_completionEqAt_iff_eq
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) :
    (∀ n : Nat, CompletionEqAt D n x y) ↔ x = y := by
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t
  constructor
  · intro hall
    apply Quotient.sound
    change ObservationalSequenceEq D s.term t.term
    intro n
    exact hall n
  · intro hxy
    have hrel := Quotient.exact hxy
    change ObservationalSequenceEq D s.term t.term at hrel
    exact hrel

/-- At every finite stage, the embedded generated Answers are dense in the
    observational completion. A Cauchy representative supplies a late term
    that approximates its class at that stage. -/
theorem observationalCompletionEmbed_stage_dense
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (q : ObservationalCompletion D) :
    ∃ x : Free.GeneratedAns D,
      CompletionEqAt D n q
        (observationalCompletionEmbed D x) := by
  refine Quotient.inductionOn q ?_
  intro s
  rcases s.cauchy n with ⟨N, hN⟩
  refine ⟨s.term N, ?_⟩
  change ObservationalSequenceEqAt D n
    s.term (fun _ => s.term N)
  exact ⟨N, fun k hk =>
    hN k N hk (Nat.le_refl N)⟩
/-- Convergence of a sequence of completion points in the finite-stage
    observational filtration. -/
def CompletionConverges
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → ObservationalCompletion D)
    (x : ObservationalCompletion D) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ k : Nat, N ≤ k →
      CompletionEqAt D n x (s k)

/-- Cauchy property for sequences of completion points. -/
def CompletionCauchy
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → ObservationalCompletion D) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ i j : Nat, N ≤ i → N ≤ j →
      CompletionEqAt D n (s i) (s j)

/-- Constant sequences in the completion converge. -/
theorem completionConverges_const
    (D : PartialAlg.{u,v} Sigma)
    (x : ObservationalCompletion D) :
    CompletionConverges D (fun _ => x) x := by
  intro n
  exact ⟨0, fun k hk => completionEqAt_refl D n x⟩

/-- Every convergent completion sequence is Cauchy. -/
theorem completionConverges_implies_cauchy
    (D : PartialAlg.{u,v} Sigma)
    {s : Nat → ObservationalCompletion D}
    {x : ObservationalCompletion D}
    (hs : CompletionConverges D s x) :
    CompletionCauchy D s := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact completionEqAt_trans D n
    (completionEqAt_symm D n (hN i hi))
    (hN j hj)

/-- Completion limits are unique. -/
theorem completionConverges_unique
    (D : PartialAlg.{u,v} Sigma)
    {s : Nat → ObservationalCompletion D}
    {x y : ObservationalCompletion D}
    (hx : CompletionConverges D s x)
    (hy : CompletionConverges D s y) :
    x = y := by
  apply (forall_completionEqAt_iff_eq D x y).1
  intro n
  rcases hx n with ⟨Nx, hxN⟩
  rcases hy n with ⟨Ny, hyN⟩
  let k := Nat.max Nx Ny
  have hxk : CompletionEqAt D n x (s k) :=
    hxN k (Nat.le_max_left Nx Ny)
  have hyk : CompletionEqAt D n y (s k) :=
    hyN k (Nat.le_max_right Nx Ny)
  exact completionEqAt_trans D n hxk
    (completionEqAt_symm D n hyk)

/-- At stage `k`, choose one generated Answer approximating the `k`th
    completion point to stage `k`. -/
noncomputable def completionApproximation
    (D : PartialAlg.{u,v} Sigma)
    (q : Nat → ObservationalCompletion D)
    (k : Nat) : Free.GeneratedAns D :=
  Classical.choose
    (observationalCompletionEmbed_stage_dense D k (q k))

theorem completionApproximation_spec
    (D : PartialAlg.{u,v} Sigma)
    (q : Nat → ObservationalCompletion D)
    (k : Nat) :
    CompletionEqAt D k (q k)
      (observationalCompletionEmbed D
        (completionApproximation D q k)) :=
  Classical.choose_spec
    (observationalCompletionEmbed_stage_dense D k (q k))

/-- Diagonal finite-stage approximants of a Cauchy completion sequence form an
    observationally Cauchy sequence of generated Answers. -/
theorem completionApproximation_cauchy
    (D : PartialAlg.{u,v} Sigma)
    {q : Nat → ObservationalCompletion D}
    (hq : CompletionCauchy D q) :
    ObservationalCauchy D
      (fun k => completionApproximation D q k) := by
  intro n
  rcases hq n with ⟨N, hN⟩
  refine ⟨Nat.max N n, ?_⟩
  intro i j hi hj
  have hNi : N ≤ i :=
    Nat.le_trans (Nat.le_max_left N n) hi
  have hNj : N ≤ j :=
    Nat.le_trans (Nat.le_max_left N n) hj
  have hni : n ≤ i :=
    Nat.le_trans (Nat.le_max_right N n) hi
  have hnj : n ≤ j :=
    Nat.le_trans (Nat.le_max_right N n) hj
  have hiApprox :
      CompletionEqAt D n (q i)
        (observationalCompletionEmbed D
          (completionApproximation D q i)) :=
    completionEqAt_antitone D hni
      (completionApproximation_spec D q i)
  have hjApprox :
      CompletionEqAt D n (q j)
        (observationalCompletionEmbed D
          (completionApproximation D q j)) :=
    completionEqAt_antitone D hnj
      (completionApproximation_spec D q j)
  have hij :
      CompletionEqAt D n
        (observationalCompletionEmbed D
          (completionApproximation D q i))
        (observationalCompletionEmbed D
          (completionApproximation D q j)) :=
    completionEqAt_trans D n
      (completionEqAt_symm D n hiApprox)
      (completionEqAt_trans D n
        (hN i j hNi hNj) hjApprox)
  exact (completionEqAt_embed_iff D n
    (completionApproximation D q i)
    (completionApproximation D q j)).1 hij

/-- The packaged diagonal Cauchy representative. -/
noncomputable def completionDiagonalSeq
    (D : PartialAlg.{u,v} Sigma)
    (q : Nat → ObservationalCompletion D)
    (hq : CompletionCauchy D q) :
    ObservationalCauchySeq D where
  term := fun k => completionApproximation D q k
  cauchy := completionApproximation_cauchy D hq

/-- Canonical diagonal limit of a Cauchy sequence in the completion. -/
noncomputable def completionLimit
    (D : PartialAlg.{u,v} Sigma)
    (q : Nat → ObservationalCompletion D)
    (hq : CompletionCauchy D q) :
    ObservationalCompletion D :=
  observationalCompletionClass D
    (completionDiagonalSeq D q hq)

/-- A represented completion class and an embedded original point are related
    at stage `n` exactly when their representative sequence is eventually in
    the corresponding original stage ball. -/
theorem completionEqAt_class_embed_iff
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (s : ObservationalCauchySeq D)
    (x : Free.GeneratedAns D) :
    CompletionEqAt D n
        (observationalCompletionClass D s)
        (observationalCompletionEmbed D x) ↔
      ObservationalSequenceEqAt D n s.term (fun _ => x) := by
  rfl

/-- The diagonal class is a limit of the original completion-valued Cauchy
    sequence. -/
theorem completionConverges_to_completionLimit
    (D : PartialAlg.{u,v} Sigma)
    {q : Nat → ObservationalCompletion D}
    (hq : CompletionCauchy D q) :
    CompletionConverges D q (completionLimit D q hq) := by
  intro n
  have ha :
      ObservationalCauchy D
        (fun k => completionApproximation D q k) :=
    completionApproximation_cauchy D hq
  rcases ha n with ⟨M, hM⟩
  refine ⟨Nat.max M n, ?_⟩
  intro k hk
  have hMk : M ≤ k :=
    Nat.le_trans (Nat.le_max_left M n) hk
  have hnk : n ≤ k :=
    Nat.le_trans (Nat.le_max_right M n) hk
  have hclassEmbed :
      CompletionEqAt D n
        (completionLimit D q hq)
        (observationalCompletionEmbed D
          (completionApproximation D q k)) := by
    apply (completionEqAt_class_embed_iff D n
      (completionDiagonalSeq D q hq)
      (completionApproximation D q k)).2
    change ObservationalSequenceEqAt D n
      (fun j => completionApproximation D q j)
      (fun _ => completionApproximation D q k)
    exact ⟨M, fun j hj => hM j k hj hMk⟩
  have hqEmbed :
      CompletionEqAt D n (q k)
        (observationalCompletionEmbed D
          (completionApproximation D q k)) :=
    completionEqAt_antitone D hnk
      (completionApproximation_spec D q k)
  exact completionEqAt_trans D n hclassEmbed
    (completionEqAt_symm D n hqEmbed)

/-- Completeness of a space described by the completion-stage filtration. -/
def CompletionComplete
    (D : PartialAlg.{u,v} Sigma) : Prop :=
  ∀ q : Nat → ObservationalCompletion D,
    CompletionCauchy D q →
      ∃ x : ObservationalCompletion D,
        CompletionConverges D q x

/-- The Cauchy-sequence quotient is complete. -/
theorem observationalCompletion_is_complete
    (D : PartialAlg.{u,v} Sigma) :
    CompletionComplete D := by
  intro q hq
  exact ⟨completionLimit D q hq,
    completionConverges_to_completionLimit D hq⟩
/-- Every Cauchy representative converges, after embedding its terms, to its
    own completion class. This is the sequential form of density. -/
theorem observationalCompletion_embed_sequence_converges
    (D : PartialAlg.{u,v} Sigma)
    (s : ObservationalCauchySeq D) :
    CompletionConverges D
      (fun k => observationalCompletionEmbed D (s.term k))
      (observationalCompletionClass D s) := by
  intro n
  rcases s.cauchy n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  apply (completionEqAt_class_embed_iff D n s (s.term k)).2
  exact ⟨N, fun j hj => hN j k hj hk⟩

/-- The embedded generated Answers are sequentially dense in the completion:
    every completion point is the limit of an embedded observationally Cauchy
    sequence. -/
theorem observationalCompletion_sequentially_dense
    (D : PartialAlg.{u,v} Sigma)
    (q : ObservationalCompletion D) :
    ∃ s : ObservationalCauchySeq D,
      CompletionConverges D
        (fun k => observationalCompletionEmbed D (s.term k)) q := by
  refine Quotient.inductionOn q ?_
  intro s
  exact ⟨s, observationalCompletion_embed_sequence_converges D s⟩

/-- Completeness of the original generated-Answer space makes the canonical
    completion embedding surjective. -/
theorem observationalComplete_implies_completionEmbed_surjective
    (D : PartialAlg.{u,v} Sigma)
    (hD : ObservationalComplete D) :
    Function.Surjective (observationalCompletionEmbed D) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro s
  change ∃ x : Free.GeneratedAns D,
    observationalCompletionEmbed D x =
      observationalCompletionClass D s
  rcases hD s.term s.cauchy with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  exact ((observationalCompletionClass_eq_embed_iff D s x).2 hx).symm

/-- Conversely, surjectivity of the completion embedding forces every
    observationally Cauchy sequence of generated Answers to converge. -/
theorem completionEmbed_surjective_implies_observationalComplete
    (D : PartialAlg.{u,v} Sigma)
    (hSurj : Function.Surjective
      (observationalCompletionEmbed D)) :
    ObservationalComplete D := by
  intro t ht
  let s : ObservationalCauchySeq D :=
    { term := t, cauchy := ht }
  rcases hSurj (observationalCompletionClass D s) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hclass :
      observationalCompletionClass D s =
        observationalCompletionEmbed D x := hx.symm
  have hconv :=
    (observationalCompletionClass_eq_embed_iff D s x).1 hclass
  simpa [s] using hconv

/-- The original space is observationally complete exactly when its canonical
    embedding fills the entire Cauchy completion. -/
theorem observationalComplete_iff_completionEmbed_surjective
    (D : PartialAlg.{u,v} Sigma) :
    ObservationalComplete D ↔
      Function.Surjective (observationalCompletionEmbed D) := by
  constructor
  · exact observationalComplete_implies_completionEmbed_surjective D
  · exact completionEmbed_surjective_implies_observationalComplete D

/-- Since the completion embedding is always injective, completeness of the
    original generated-Answer space is equivalent to the conjunction of
    injectivity and surjectivity. -/
theorem observationalComplete_iff_completionEmbed_inverse_data
    (D : PartialAlg.{u,v} Sigma) :
    ObservationalComplete D ↔
      Function.Injective (observationalCompletionEmbed D) ∧
        Function.Surjective (observationalCompletionEmbed D) := by
  constructor
  · intro hD
    exact ⟨observationalCompletionEmbed_injective D,
      observationalComplete_implies_completionEmbed_surjective D hD⟩
  · intro hData
    exact completionEmbed_surjective_implies_observationalComplete D hData.2

/-- Under observational completeness, choose the unique original generated
    Answer represented by a completion point. -/
noncomputable def observationalCompletionInverse
    (D : PartialAlg.{u,v} Sigma)
    (hD : ObservationalComplete D)
    (q : ObservationalCompletion D) :
    Free.GeneratedAns D :=
  Classical.choose
    (observationalComplete_implies_completionEmbed_surjective D hD q)

/-- Embedding after the chosen inverse returns the original completion point. -/
theorem observationalCompletionEmbed_inverse_right
    (D : PartialAlg.{u,v} Sigma)
    (hD : ObservationalComplete D)
    (q : ObservationalCompletion D) :
    observationalCompletionEmbed D
        (observationalCompletionInverse D hD q) = q :=
  Classical.choose_spec
    (observationalComplete_implies_completionEmbed_surjective D hD q)

/-- The chosen inverse after embedding returns the original generated Answer. -/
theorem observationalCompletionEmbed_inverse_left
    (D : PartialAlg.{u,v} Sigma)
    (hD : ObservationalComplete D)
    (x : Free.GeneratedAns D) :
    observationalCompletionInverse D hD
        (observationalCompletionEmbed D x) = x := by
  apply observationalCompletionEmbed_injective D
  exact observationalCompletionEmbed_inverse_right D hD
    (observationalCompletionEmbed D x)
/-- Distinct completion points separate at some finite observational stage. -/
theorem completionSeparatingStage_exists
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D}
    (hxy : x ≠ y) :
    ∃ n : Nat, ¬ CompletionEqAt D n x y := by
  classical
  by_cases hsep : ∃ n : Nat, ¬ CompletionEqAt D n x y
  · exact hsep
  · have hall : ∀ n : Nat, CompletionEqAt D n x y := by
      intro n
      by_cases hn : CompletionEqAt D n x y
      · exact hn
      · exact False.elim (hsep ⟨n, hn⟩)
    exact False.elim (hxy ((forall_completionEqAt_iff_eq D x y).1 hall))

/-- Every unequal pair of completion points has a least separating stage. -/
theorem completionSeparationRank_witness_exists
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D}
    (hxy : x ≠ y) :
    ∃ r : Nat,
      (¬ CompletionEqAt D r x y) ∧
      ∀ m : Nat, (¬ CompletionEqAt D m x y) → r ≤ m := by
  rcases completionSeparatingStage_exists D hxy with ⟨B, hB⟩
  rcases exists_least_bounded
      (p := fun n => ¬ CompletionEqAt D n x y) B hB with
    ⟨r, hrB, hr, hmin⟩
  exact ⟨r, hr, hmin⟩

/-- Least finite observational stage separating two completion points. Equal
    points receive rank zero by convention. -/
noncomputable def completionSeparationRank
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) : Nat := by
  classical
  exact if h : x ≠ y then
    Classical.choose (completionSeparationRank_witness_exists D h)
  else
    0

@[simp] theorem completionSeparationRank_eq_zero_of_eq
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D} (hxy : x = y) :
    completionSeparationRank D x y = 0 := by
  classical
  subst y
  simp [completionSeparationRank]

/-- A distinct pair fails finite-stage agreement at its completion separation
    rank. -/
theorem not_completionEqAt_at_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D} (hxy : x ≠ y) :
    ¬ CompletionEqAt D (completionSeparationRank D x y) x y := by
  classical
  have hspec := Classical.choose_spec
    (completionSeparationRank_witness_exists D hxy)
  simpa [completionSeparationRank, hxy] using hspec.1

/-- The completion separation rank is minimal among all separating stages. -/
theorem completionSeparationRank_minimal
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D} (hxy : x ≠ y)
    {n : Nat} (hn : ¬ CompletionEqAt D n x y) :
    completionSeparationRank D x y ≤ n := by
  classical
  have hspec := Classical.choose_spec
    (completionSeparationRank_witness_exists D hxy)
  simpa [completionSeparationRank, hxy] using hspec.2 n hn

/-- Completion separation rank is symmetric. -/
theorem completionSeparationRank_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) :
    completionSeparationRank D x y =
      completionSeparationRank D y x := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    apply Nat.le_antisymm
    · apply completionSeparationRank_minimal D hxy
      intro hEq
      exact (not_completionEqAt_at_rank D hyx)
        (completionEqAt_symm D
          (completionSeparationRank D y x) hEq)
    · apply completionSeparationRank_minimal D hyx
      intro hEq
      exact (not_completionEqAt_at_rank D hxy)
        (completionEqAt_symm D
          (completionSeparationRank D x y) hEq)

/-- For a distinct pair, completion points agree exactly below their least
    separating stage. -/
theorem completionEqAt_iff_lt_rank
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D} (hxy : x ≠ y)
    (n : Nat) :
    CompletionEqAt D n x y ↔
      n < completionSeparationRank D x y := by
  classical
  constructor
  · intro hEq
    apply Nat.lt_of_not_ge
    intro hRank
    have hAtRank :
        CompletionEqAt D (completionSeparationRank D x y) x y :=
      completionEqAt_antitone D hRank hEq
    exact (not_completionEqAt_at_rank D hxy) hAtRank
  · intro hlt
    by_cases hEq : CompletionEqAt D n x y
    · exact hEq
    · have hmin := completionSeparationRank_minimal D hxy hEq
      exact False.elim ((Nat.not_le_of_gt hlt) hmin)

/-- Uniform completion-stage threshold law, including equality. -/
theorem completionEqAt_iff_eq_or_lt_rank
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat) (x y : ObservationalCompletion D) :
    CompletionEqAt D n x y ↔
      x = y ∨ n < completionSeparationRank D x y := by
  classical
  by_cases hxy : x = y
  · subst y
    constructor
    · intro hEq
      exact Or.inl rfl
    · intro h
      exact completionEqAt_refl D n x
  · constructor
    · intro hEq
      exact Or.inr ((completionEqAt_iff_lt_rank D hxy n).1 hEq)
    · intro h
      cases h with
      | inl heq => exact False.elim (hxy heq)
      | inr hlt => exact (completionEqAt_iff_lt_rank D hxy n).2 hlt

/-- Non-Archimedean rank inequality on the completion. -/
theorem completionSeparationRank_min_triangle
    (D : PartialAlg.{u,v} Sigma)
    (x y z : ObservationalCompletion D) (hxz : x ≠ z) :
    Nat.min (completionSeparationRank D x y)
        (completionSeparationRank D y z) ≤
      completionSeparationRank D x z := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hyz : y = z
    · subst z
      simp
    · by_cases hle :
          Nat.min (completionSeparationRank D x y)
              (completionSeparationRank D y z) ≤
            completionSeparationRank D x z
      · exact hle
      · have hltMin :
            completionSeparationRank D x z <
              Nat.min (completionSeparationRank D x y)
                (completionSeparationRank D y z) :=
          Nat.lt_of_not_ge hle
        have hltXY :
            completionSeparationRank D x z <
              completionSeparationRank D x y :=
          Nat.lt_of_lt_of_le hltMin (Nat.min_le_left _ _)
        have hltYZ :
            completionSeparationRank D x z <
              completionSeparationRank D y z :=
          Nat.lt_of_lt_of_le hltMin (Nat.min_le_right _ _)
        have hEqXY :
            CompletionEqAt D (completionSeparationRank D x z) x y :=
          (completionEqAt_iff_lt_rank D hxy
            (completionSeparationRank D x z)).2 hltXY
        have hEqYZ :
            CompletionEqAt D (completionSeparationRank D x z) y z :=
          (completionEqAt_iff_lt_rank D hyz
            (completionSeparationRank D x z)).2 hltYZ
        have hEqXZ :
            CompletionEqAt D (completionSeparationRank D x z) x z :=
          completionEqAt_trans D
            (completionSeparationRank D x z) hEqXY hEqYZ
        exact False.elim
          ((not_completionEqAt_at_rank D hxz) hEqXZ)

/-- Extended observational depth on the completion. -/
noncomputable def completionDepth
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) : SeparationDepth := by
  classical
  exact if h : x = y then
    .infinity
  else
    .finite (completionSeparationRank D x y)

@[simp] theorem completionDepth_self
    (D : PartialAlg.{u,v} Sigma)
    (x : ObservationalCompletion D) :
    completionDepth D x x = .infinity := by
  classical
  simp [completionDepth]

@[simp] theorem completionDepth_of_ne
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D} (hxy : x ≠ y) :
    completionDepth D x y =
      .finite (completionSeparationRank D x y) := by
  classical
  simp [completionDepth, hxy]

theorem completionDepth_eq_infinity_iff
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) :
    completionDepth D x y = .infinity ↔ x = y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionDepth]
  · simp [completionDepth, hxy]

theorem completionDepth_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) :
    completionDepth D x y = completionDepth D y x := by
  classical
  by_cases hxy : x = y
  · subst y
    rfl
  · have hyx : y ≠ x := Ne.symm hxy
    simp [completionDepth, hxy, hyx,
      completionSeparationRank_symm D x y]

/-- Total non-Archimedean depth law on the completion. -/
theorem completionDepth_min_triangle
    (D : PartialAlg.{u,v} Sigma)
    (x y z : ObservationalCompletion D) :
    SeparationDepth.le
      (SeparationDepth.min
        (completionDepth D x y)
        (completionDepth D y z))
      (completionDepth D x z) := by
  classical
  by_cases hxz : x = z
  · subst z
    by_cases hxy : x = y
    · subst y
      simp [completionDepth,
        SeparationDepth.min, SeparationDepth.le]
    · have hyx : y ≠ x := Ne.symm hxy
      simp [completionDepth, hxy, hyx,
        SeparationDepth.min, SeparationDepth.le]
  · by_cases hxy : x = y
    · subst y
      simp [completionDepth, hxz,
        SeparationDepth.min, SeparationDepth.le]
    · by_cases hyz : y = z
      · subst z
        simp [completionDepth, hxy,
          SeparationDepth.min, SeparationDepth.le]
      · simpa [completionDepth, hxy, hyz, hxz,
          SeparationDepth.min, SeparationDepth.le] using
          (completionSeparationRank_min_triangle D x y z hxz)

/-- Symbolic discrete ultrametric on the completion. -/
noncomputable def completionDistance
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) : SeparationDistance :=
  SeparationDistance.ofDepth (completionDepth D x y)

@[simp] theorem completionDistance_self
    (D : PartialAlg.{u,v} Sigma)
    (x : ObservationalCompletion D) :
    completionDistance D x x = .zero := by
  simp [completionDistance]

@[simp] theorem completionDistance_of_ne
    (D : PartialAlg.{u,v} Sigma)
    {x y : ObservationalCompletion D} (hxy : x ≠ y) :
    completionDistance D x y =
      .level (completionSeparationRank D x y) := by
  simp [completionDistance, completionDepth_of_ne D hxy]

theorem completionDistance_eq_zero_iff
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) :
    completionDistance D x y = .zero ↔ x = y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionDistance]
  · simp [completionDistance, completionDepth,
      SeparationDistance.ofDepth, hxy]

theorem completionDistance_symm
    (D : PartialAlg.{u,v} Sigma)
    (x y : ObservationalCompletion D) :
    completionDistance D x y = completionDistance D y x := by
  unfold completionDistance
  rw [completionDepth_symm D x y]

/-- Strong ultrametric inequality on the completion. -/
theorem completionDistance_strong_triangle
    (D : PartialAlg.{u,v} Sigma)
    (x y z : ObservationalCompletion D) :
    SeparationDistance.le
      (completionDistance D x z)
      (SeparationDistance.max
        (completionDistance D x y)
        (completionDistance D y z)) := by
  apply SeparationDistance.ofDepth_strong_triangle
  exact completionDepth_min_triangle D x y z

/-- The observational completion carries the canonical completed discrete
    ultrametric. -/
noncomputable def observationalCompletionDiscreteUltrametric
    (D : PartialAlg.{u,v} Sigma) :
    DiscreteUltrametric (ObservationalCompletion D) where
  distance := completionDistance D
  eq_zero := completionDistance_eq_zero_iff D
  symm := completionDistance_symm D
  strong_triangle := completionDistance_strong_triangle D

/-- The completion separation rank restricts to the original finite separation
    rank along the canonical embedding. -/
theorem completionSeparationRank_embed
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    completionSeparationRank D
        (observationalCompletionEmbed D x)
        (observationalCompletionEmbed D y) =
      finiteSeparationRank D x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionSeparationRank, finiteSeparationRank]
  · have hEmb :
        observationalCompletionEmbed D x ≠
          observationalCompletionEmbed D y := by
      intro h
      exact hxy (observationalCompletionEmbed_injective D h)
    apply Nat.le_antisymm
    · apply completionSeparationRank_minimal D hEmb
      intro hEq
      have hOrig := (completionEqAt_embed_iff D
        (finiteSeparationRank D x y) x y).1 hEq
      exact (not_finiteTagEqAt_at_rank D hxy)
        (by simpa [FiniteObservationBall] using hOrig)
    · apply Nat.le_of_not_gt
      intro hlt
      have hOrigEq :
          FiniteObservationBall D
            (completionSeparationRank D
              (observationalCompletionEmbed D x)
              (observationalCompletionEmbed D y)) x y := by
        simpa [FiniteObservationBall] using
          (finiteTagEqAt_of_lt_rank D hxy hlt)
      have hCompEq := (completionEqAt_embed_iff D
        (completionSeparationRank D
          (observationalCompletionEmbed D x)
          (observationalCompletionEmbed D y)) x y).2 hOrigEq
      exact (not_completionEqAt_at_rank D hEmb) hCompEq

/-- The completion embedding preserves observational depth exactly. -/
theorem completionDepth_embed
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    completionDepth D
        (observationalCompletionEmbed D x)
        (observationalCompletionEmbed D y) =
      observationalDepth D x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionDepth, observationalDepth]
  · have hEmb :
        observationalCompletionEmbed D x ≠
          observationalCompletionEmbed D y := by
      intro h
      exact hxy (observationalCompletionEmbed_injective D h)
    simp [completionDepth, observationalDepth, hxy, hEmb,
      completionSeparationRank_embed D x y]

/-- The canonical embedding is isometric for the symbolic observational
    ultrametric. -/
theorem completionDistance_embed
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    completionDistance D
        (observationalCompletionEmbed D x)
        (observationalCompletionEmbed D y) =
      observationalDistance D x y := by
  unfold completionDistance observationalDistance
  rw [completionDepth_embed D x y]
/-- A map is observationally nonexpansive when it preserves every finite-stage
    indistinguishability relation. -/
structure ObservationalNonexpansive
    (A B : PartialAlg.{u,v} Sigma) where
  toFun : Free.GeneratedAns A → Free.GeneratedAns B
  map_stage : ∀ n : Nat, ∀ {x y : Free.GeneratedAns A},
    FiniteObservationBall A n x y →
      FiniteObservationBall B n (toFun x) (toFun y)

/-- An observationally nonexpansive map sends Cauchy sequences to Cauchy
    sequences. -/
theorem observationalNonexpansive_map_cauchy
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    {s : Nat → Free.GeneratedAns A}
    (hs : ObservationalCauchy A s) :
    ObservationalCauchy B (fun k => f.toFun (s k)) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact f.map_stage n (hN i j hi hj)

/-- Pointwise application preserves full asymptotic sequence equivalence. -/
theorem observationalNonexpansive_map_sequenceEq
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    {s t : Nat → Free.GeneratedAns A}
    (hst : ObservationalSequenceEq A s t) :
    ObservationalSequenceEq B
      (fun k => f.toFun (s k))
      (fun k => f.toFun (t k)) := by
  intro n
  rcases hst n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact f.map_stage n (hN k hk)

/-- Pointwise application also preserves one fixed asymptotic stage. -/
theorem observationalNonexpansive_map_sequenceEqAt
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (n : Nat)
    {s t : Nat → Free.GeneratedAns A}
    (hst : ObservationalSequenceEqAt A n s t) :
    ObservationalSequenceEqAt B n
      (fun k => f.toFun (s k))
      (fun k => f.toFun (t k)) := by
  rcases hst with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact f.map_stage n (hN k hk)

/-- Pointwise image of a packaged Cauchy representative. -/
def mapObservationalCauchySeq
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (s : ObservationalCauchySeq A) :
    ObservationalCauchySeq B where
  term := fun k => f.toFun (s.term k)
  cauchy := observationalNonexpansive_map_cauchy f s.cauchy

/-- Every observationally nonexpansive map extends canonically to Cauchy
    completions by pointwise action on representatives. -/
def observationalCompletionMap
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (q : ObservationalCompletion A) :
    ObservationalCompletion B :=
  Quotient.liftOn q
    (fun s => observationalCompletionClass B
      (mapObservationalCauchySeq f s))
    (by
      intro s t hst
      apply Quotient.sound
      change ObservationalSequenceEq A s.term t.term at hst
      exact observationalNonexpansive_map_sequenceEq f hst)

/-- The completion extension agrees with the original map on embedded generated
    Answers. -/
theorem observationalCompletionMap_embed
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (x : Free.GeneratedAns A) :
    observationalCompletionMap f
        (observationalCompletionEmbed A x) =
      observationalCompletionEmbed B (f.toFun x) := by
  apply Quotient.sound
  exact observationalSequenceEq_refl B (fun _ => f.toFun x)

/-- The completion extension remains nonexpansive at every completion stage. -/
theorem observationalCompletionMap_preserves_eqAt
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (n : Nat)
    {x y : ObservationalCompletion A}
    (hxy : CompletionEqAt A n x y) :
    CompletionEqAt B n
      (observationalCompletionMap f x)
      (observationalCompletionMap f y) := by
  revert hxy
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  change ObservationalSequenceEqAt A n s.term t.term at hst
  change ObservationalSequenceEqAt B n
    (fun k => f.toFun (s.term k))
    (fun k => f.toFun (t.term k))
  exact observationalNonexpansive_map_sequenceEqAt f n hst

/-- Completion extensions preserve convergence. -/
theorem observationalCompletionMap_preserves_convergence
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    {s : Nat → ObservationalCompletion A}
    {x : ObservationalCompletion A}
    (hs : CompletionConverges A s x) :
    CompletionConverges B
      (fun k => observationalCompletionMap f (s k))
      (observationalCompletionMap f x) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact observationalCompletionMap_preserves_eqAt f n (hN k hk)

/-- Completion extensions preserve Cauchy sequences. -/
theorem observationalCompletionMap_preserves_cauchy
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    {s : Nat → ObservationalCompletion A}
    (hs : CompletionCauchy A s) :
    CompletionCauchy B
      (fun k => observationalCompletionMap f (s k)) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact observationalCompletionMap_preserves_eqAt f n
    (hN i j hi hj)

/-- Identity observational map. -/
def observationalNonexpansiveId
    (A : PartialAlg.{u,v} Sigma) :
    ObservationalNonexpansive A A where
  toFun := fun x => x
  map_stage := by
    intro n x y hxy
    exact hxy

/-- Composition of observationally nonexpansive maps. -/
def observationalNonexpansiveComp
    {A B C : PartialAlg.{u,v} Sigma}
    (g : ObservationalNonexpansive B C)
    (f : ObservationalNonexpansive A B) :
    ObservationalNonexpansive A C where
  toFun := fun x => g.toFun (f.toFun x)
  map_stage := by
    intro n x y hxy
    exact g.map_stage n (f.map_stage n hxy)

/-- Completion sends the identity map to the identity map. -/
theorem observationalCompletionMap_id
    (A : PartialAlg.{u,v} Sigma)
    (q : ObservationalCompletion A) :
    observationalCompletionMap
        (observationalNonexpansiveId A) q = q := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  exact observationalSequenceEq_refl A s.term

/-- Completion respects composition. -/
theorem observationalCompletionMap_comp
    {A B C : PartialAlg.{u,v} Sigma}
    (g : ObservationalNonexpansive B C)
    (f : ObservationalNonexpansive A B)
    (q : ObservationalCompletion A) :
    observationalCompletionMap
        (observationalNonexpansiveComp g f) q =
      observationalCompletionMap g
        (observationalCompletionMap f q) := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  exact observationalSequenceEq_refl C
    (fun k => g.toFun (f.toFun (s.term k)))
/-- A completion map cannot create a separating stage earlier than the source
    map. For distinct images, source separation rank is therefore bounded by
    target separation rank. -/
theorem observationalCompletionMap_rank_mono
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    {x y : ObservationalCompletion A}
    (hmap : observationalCompletionMap f x ≠
      observationalCompletionMap f y) :
    completionSeparationRank A x y ≤
      completionSeparationRank B
        (observationalCompletionMap f x)
        (observationalCompletionMap f y) := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hmap rfl
  apply Nat.le_of_not_gt
  intro hlt
  have hSource :
      CompletionEqAt A
        (completionSeparationRank B
          (observationalCompletionMap f x)
          (observationalCompletionMap f y)) x y :=
    (completionEqAt_iff_lt_rank A hxy
      (completionSeparationRank B
        (observationalCompletionMap f x)
        (observationalCompletionMap f y))).2 hlt
  have hTarget :=
    observationalCompletionMap_preserves_eqAt f
      (completionSeparationRank B
        (observationalCompletionMap f x)
        (observationalCompletionMap f y)) hSource
  exact (not_completionEqAt_at_rank B hmap) hTarget

/-- Observational depth can only increase under a completion extension. -/
theorem observationalCompletionMap_depth_mono
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (x y : ObservationalCompletion A) :
    SeparationDepth.le
      (completionDepth A x y)
      (completionDepth B
        (observationalCompletionMap f x)
        (observationalCompletionMap f y)) := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionDepth, SeparationDepth.le]
  · by_cases hmap : observationalCompletionMap f x =
        observationalCompletionMap f y
    · simp [completionDepth, hxy, hmap, SeparationDepth.le]
    · simpa [completionDepth, hxy, hmap, SeparationDepth.le] using
        (observationalCompletionMap_rank_mono f hmap)

namespace SeparationDistance

/-- Converting similarity depth to symbolic distance reverses the depth order. -/
theorem ofDepth_antitone {a b : SeparationDepth}
    (h : SeparationDepth.le a b) :
    le (ofDepth b) (ofDepth a) := by
  cases a <;> cases b <;>
    simpa [SeparationDepth.le, le, ofDepth] using h

end SeparationDistance

/-- Every completion extension is nonexpansive for the completed symbolic
    ultrametrics. -/
theorem observationalCompletionMap_distance_nonexpansive
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (x y : ObservationalCompletion A) :
    SeparationDistance.le
      (completionDistance B
        (observationalCompletionMap f x)
        (observationalCompletionMap f y))
      (completionDistance A x y) := by
  unfold completionDistance
  exact SeparationDistance.ofDepth_antitone
    (observationalCompletionMap_depth_mono f x y)

/-- The original observationally nonexpansive map is itself nonexpansive for
    the finite-tag symbolic ultrametrics. -/
theorem observationalNonexpansive_distance
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (x y : Free.GeneratedAns A) :
    SeparationDistance.le
      (observationalDistance B (f.toFun x) (f.toFun y))
      (observationalDistance A x y) := by
  have h := observationalCompletionMap_distance_nonexpansive f
    (observationalCompletionEmbed A x)
    (observationalCompletionEmbed A y)
  rw [observationalCompletionMap_embed,
    observationalCompletionMap_embed,
    completionDistance_embed,
    completionDistance_embed] at h
  exact h
/-- A stage embedding preserves and reflects every finite observational stage. -/
structure ObservationalStageEmbedding
    (A B : PartialAlg.{u,v} Sigma) where
  toFun : Free.GeneratedAns A → Free.GeneratedAns B
  map_stage : ∀ n : Nat, ∀ {x y : Free.GeneratedAns A},
    FiniteObservationBall A n x y →
      FiniteObservationBall B n (toFun x) (toFun y)
  reflect_stage : ∀ n : Nat, ∀ {x y : Free.GeneratedAns A},
    FiniteObservationBall B n (toFun x) (toFun y) →
      FiniteObservationBall A n x y

namespace ObservationalStageEmbedding

/-- Forget reflection and retain the nonexpansive map. -/
def toNonexpansive
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B) :
    ObservationalNonexpansive A B where
  toFun := f.toFun
  map_stage := f.map_stage

end ObservationalStageEmbedding

/-- A stage embedding is injective on generated Answers. -/
theorem observationalStageEmbedding_injective
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B) :
    Function.Injective f.toFun := by
  intro x y hxy
  apply (all_finiteObservationBalls_iff_eq A x y).1
  intro n
  apply f.reflect_stage n
  rw [hxy]
  exact finiteObservationBall_center B n (f.toFun y)

/-- Stage embeddings reflect eventual agreement at one fixed stage. -/
theorem observationalStageEmbedding_reflect_sequenceEqAt
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (n : Nat)
    {s t : Nat → Free.GeneratedAns A}
    (hst : ObservationalSequenceEqAt B n
      (fun k => f.toFun (s k))
      (fun k => f.toFun (t k))) :
    ObservationalSequenceEqAt A n s t := by
  rcases hst with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact f.reflect_stage n (hN k hk)

/-- The completion extension of a stage embedding reflects each completed
    finite stage. -/
theorem observationalStageEmbedding_completionMap_reflects_eqAt
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (n : Nat)
    {x y : ObservationalCompletion A}
    (hxy : CompletionEqAt B n
      (observationalCompletionMap f.toNonexpansive x)
      (observationalCompletionMap f.toNonexpansive y)) :
    CompletionEqAt A n x y := by
  revert hxy
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  change ObservationalSequenceEqAt B n
    (fun k => f.toFun (s.term k))
    (fun k => f.toFun (t.term k)) at hst
  change ObservationalSequenceEqAt A n s.term t.term
  exact observationalStageEmbedding_reflect_sequenceEqAt f n hst

/-- The completion extension of a stage embedding preserves and reflects every
    completed finite stage. -/
theorem observationalStageEmbedding_completionMap_eqAt_iff
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (n : Nat)
    (x y : ObservationalCompletion A) :
    CompletionEqAt B n
        (observationalCompletionMap f.toNonexpansive x)
        (observationalCompletionMap f.toNonexpansive y) ↔
      CompletionEqAt A n x y := by
  constructor
  · exact observationalStageEmbedding_completionMap_reflects_eqAt f n
  · exact observationalCompletionMap_preserves_eqAt f.toNonexpansive n

/-- The induced completion map of a stage embedding is injective. -/
theorem observationalStageEmbedding_completionMap_injective
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B) :
    Function.Injective
      (observationalCompletionMap f.toNonexpansive) := by
  intro x y hxy
  apply (forall_completionEqAt_iff_eq A x y).1
  intro n
  apply observationalStageEmbedding_completionMap_reflects_eqAt f n
  rw [hxy]

/-- Completion separation rank is preserved exactly by stage embeddings. -/
theorem observationalStageEmbedding_completionRank
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (x y : ObservationalCompletion A) :
    completionSeparationRank B
        (observationalCompletionMap f.toNonexpansive x)
        (observationalCompletionMap f.toNonexpansive y) =
      completionSeparationRank A x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionSeparationRank]
  · have hmap :
        observationalCompletionMap f.toNonexpansive x ≠
          observationalCompletionMap f.toNonexpansive y := by
      intro h
      exact hxy
        (observationalStageEmbedding_completionMap_injective f h)
    apply Nat.le_antisymm
    · apply completionSeparationRank_minimal B hmap
      intro hAt
      have hSource :=
        observationalStageEmbedding_completionMap_reflects_eqAt f
          (completionSeparationRank A x y) hAt
      exact (not_completionEqAt_at_rank A hxy) hSource
    · exact observationalCompletionMap_rank_mono
        f.toNonexpansive hmap

/-- Completion depth is preserved exactly by stage embeddings. -/
theorem observationalStageEmbedding_completionDepth
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (x y : ObservationalCompletion A) :
    completionDepth B
        (observationalCompletionMap f.toNonexpansive x)
        (observationalCompletionMap f.toNonexpansive y) =
      completionDepth A x y := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [completionDepth]
  · have hmap :
        observationalCompletionMap f.toNonexpansive x ≠
          observationalCompletionMap f.toNonexpansive y := by
      intro h
      exact hxy
        (observationalStageEmbedding_completionMap_injective f h)
    simp [completionDepth, hxy, hmap,
      observationalStageEmbedding_completionRank f x y]

/-- The induced completion map of a stage embedding is an isometry. -/
theorem observationalStageEmbedding_completionDistance
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (x y : ObservationalCompletion A) :
    completionDistance B
        (observationalCompletionMap f.toNonexpansive x)
        (observationalCompletionMap f.toNonexpansive y) =
      completionDistance A x y := by
  unfold completionDistance
  rw [observationalStageEmbedding_completionDepth f x y]

/-- The original stage embedding is already isometric on generated Answers. -/
theorem observationalStageEmbedding_distance
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalStageEmbedding A B)
    (x y : Free.GeneratedAns A) :
    observationalDistance B (f.toFun x) (f.toFun y) =
      observationalDistance A x y := by
  have h := observationalStageEmbedding_completionDistance f
    (observationalCompletionEmbed A x)
    (observationalCompletionEmbed A y)
  rw [observationalCompletionMap_embed,
    observationalCompletionMap_embed,
    completionDistance_embed,
    completionDistance_embed] at h
  exact h
/-- Under completeness, the chosen inverse identifies finite stages in the
    completion with finite observational balls in the original space. -/
theorem observationalCompletionInverse_stage_iff
    (D : PartialAlg.{u,v} Sigma)
    (hD : ObservationalComplete D)
    (n : Nat)
    (q r : ObservationalCompletion D) :
    CompletionEqAt D n q r ↔
      FiniteObservationBall D n
        (observationalCompletionInverse D hD q)
        (observationalCompletionInverse D hD r) := by
  have h := completionEqAt_embed_iff D n
    (observationalCompletionInverse D hD q)
    (observationalCompletionInverse D hD r)
  rw [observationalCompletionEmbed_inverse_right D hD q,
    observationalCompletionEmbed_inverse_right D hD r] at h
  exact h

/-- Under completeness, the chosen inverse is an isometry from the completion
    back to the original generated-Answer space. -/
theorem observationalCompletionInverse_distance
    (D : PartialAlg.{u,v} Sigma)
    (hD : ObservationalComplete D)
    (q r : ObservationalCompletion D) :
    observationalDistance D
        (observationalCompletionInverse D hD q)
        (observationalCompletionInverse D hD r) =
      completionDistance D q r := by
  have h := completionDistance_embed D
    (observationalCompletionInverse D hD q)
    (observationalCompletionInverse D hD r)
  rw [observationalCompletionEmbed_inverse_right D hD q,
    observationalCompletionEmbed_inverse_right D hD r] at h
  exact h.symm

/-- Canonical extension of a nonexpansive map into an observationally complete
    target. First extend into the target completion, then use completeness to
    return to the original target. -/
noncomputable def observationalCompleteExtension
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (hB : ObservationalComplete B)
    (q : ObservationalCompletion A) :
    Free.GeneratedAns B :=
  observationalCompletionInverse B hB
    (observationalCompletionMap f q)

/-- The complete-target extension agrees with the original map on embedded
    generated Answers. -/
theorem observationalCompleteExtension_embed
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (hB : ObservationalComplete B)
    (x : Free.GeneratedAns A) :
    observationalCompleteExtension f hB
        (observationalCompletionEmbed A x) =
      f.toFun x := by
  unfold observationalCompleteExtension
  rw [observationalCompletionMap_embed]
  exact observationalCompletionEmbed_inverse_left B hB (f.toFun x)

/-- The complete-target extension preserves every finite completion stage. -/
theorem observationalCompleteExtension_preserves_stage
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (hB : ObservationalComplete B)
    (n : Nat)
    {q r : ObservationalCompletion A}
    (hqr : CompletionEqAt A n q r) :
    FiniteObservationBall B n
      (observationalCompleteExtension f hB q)
      (observationalCompleteExtension f hB r) := by
  change FiniteObservationBall B n
    (observationalCompletionInverse B hB
      (observationalCompletionMap f q))
    (observationalCompletionInverse B hB
      (observationalCompletionMap f r))
  apply (observationalCompletionInverse_stage_iff B hB n
    (observationalCompletionMap f q)
    (observationalCompletionMap f r)).1
  exact observationalCompletionMap_preserves_eqAt f n hqr

/-- The complete-target extension is nonexpansive. -/
theorem observationalCompleteExtension_distance_nonexpansive
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (hB : ObservationalComplete B)
    (q r : ObservationalCompletion A) :
    SeparationDistance.le
      (observationalDistance B
        (observationalCompleteExtension f hB q)
        (observationalCompleteExtension f hB r))
      (completionDistance A q r) := by
  change SeparationDistance.le
    (observationalDistance B
      (observationalCompletionInverse B hB
        (observationalCompletionMap f q))
      (observationalCompletionInverse B hB
        (observationalCompletionMap f r)))
    (completionDistance A q r)
  rw [observationalCompletionInverse_distance]
  exact observationalCompletionMap_distance_nonexpansive f q r

/-- Sequential continuity for maps from a completion back to an original
    generated-Answer space. -/
def CompletionToGeneratedContinuous
    (A B : PartialAlg.{u,v} Sigma)
    (g : ObservationalCompletion A → Free.GeneratedAns B) : Prop :=
  ∀ (s : Nat → ObservationalCompletion A)
      (x : ObservationalCompletion A),
    CompletionConverges A s x →
      ObservationalConverges B (fun k => g (s k)) (g x)

/-- The canonical complete-target extension is sequentially continuous. -/
theorem observationalCompleteExtension_continuous
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (hB : ObservationalComplete B) :
    CompletionToGeneratedContinuous A B
      (observationalCompleteExtension f hB) := by
  intro s x hs n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact observationalCompleteExtension_preserves_stage
    f hB n (hN k hk)

/-- Universal property: the canonical map is the unique sequentially
    continuous extension of `f` from the dense embedded generated Answers into
    an observationally complete target. -/
theorem observationalCompleteExtension_unique
    {A B : PartialAlg.{u,v} Sigma}
    (f : ObservationalNonexpansive A B)
    (hB : ObservationalComplete B)
    (g : ObservationalCompletion A → Free.GeneratedAns B)
    (hgEmbed : ∀ x : Free.GeneratedAns A,
      g (observationalCompletionEmbed A x) = f.toFun x)
    (hgContinuous : CompletionToGeneratedContinuous A B g) :
    g = observationalCompleteExtension f hB := by
  funext q
  rcases observationalCompletion_sequentially_dense A q with ⟨s, hs⟩
  have hgConv := hgContinuous
    (fun k => observationalCompletionEmbed A (s.term k)) q hs
  have hExtConv :=
    observationalCompleteExtension_continuous f hB
      (fun k => observationalCompletionEmbed A (s.term k)) q hs
  have hSeq :
      (fun k => g (observationalCompletionEmbed A (s.term k))) =
        (fun k => observationalCompleteExtension f hB
          (observationalCompletionEmbed A (s.term k))) := by
    funext k
    calc
      g (observationalCompletionEmbed A (s.term k)) =
          f.toFun (s.term k) := hgEmbed (s.term k)
      _ = observationalCompleteExtension f hB
          (observationalCompletionEmbed A (s.term k)) :=
        (observationalCompleteExtension_embed f hB (s.term k)).symm
  rw [hSeq] at hgConv
  exact observationalConverges_unique B hgConv hExtConv
end External

namespace Filtered

/-- A separated descending filtration of equivalence relations. This is the
    abstract structure used by finite observational semantics independently of
    Resolution syntax or partial algebras. -/
structure Space where
  Carrier : Type u
  eqAt : Nat → Carrier → Carrier → Prop
  eqAt_refl : ∀ n : Nat, ∀ x : Carrier, eqAt n x x
  eqAt_symm : ∀ n : Nat, ∀ {x y : Carrier},
    eqAt n x y → eqAt n y x
  eqAt_trans : ∀ n : Nat, ∀ {x y z : Carrier},
    eqAt n x y → eqAt n y z → eqAt n x z
  eqAt_antitone : ∀ {n m : Nat}, n ≤ m →
    ∀ {x y : Carrier}, eqAt m x y → eqAt n x y
  separated : ∀ {x y : Carrier},
    (∀ n : Nat, eqAt n x y) → x = y

/-- Agreement at every finite stage is exactly equality. -/
theorem forall_eqAt_iff_eq
    (S : Space.{u}) (x y : S.Carrier) :
    (∀ n : Nat, S.eqAt n x y) ↔ x = y := by
  constructor
  · exact S.separated
  · intro hxy
    subst y
    intro n
    exact S.eqAt_refl n x

/-- A sequence converges when it is eventually in every filtered class around
    its limit. -/
def Converges
    (S : Space.{u})
    (s : Nat → S.Carrier)
    (x : S.Carrier) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ k : Nat, N ≤ k → S.eqAt n x (s k)

/-- A sequence is Cauchy when sufficiently late terms agree at every fixed
    finite stage. -/
def Cauchy
    (S : Space.{u})
    (s : Nat → S.Carrier) : Prop :=
  ∀ n : Nat, ∃ N : Nat,
    ∀ i j : Nat, N ≤ i → N ≤ j →
      S.eqAt n (s i) (s j)

/-- Eventual agreement of two sequences at one fixed stage. -/
def SequenceEqAt
    (S : Space.{u}) (n : Nat)
    (s t : Nat → S.Carrier) : Prop :=
  ∃ N : Nat, ∀ k : Nat, N ≤ k →
    S.eqAt n (s k) (t k)

/-- Asymptotic agreement at every finite stage. -/
def SequenceEq
    (S : Space.{u})
    (s t : Nat → S.Carrier) : Prop :=
  ∀ n : Nat, SequenceEqAt S n s t

@[refl] theorem sequenceEqAt_refl
    (S : Space.{u}) (n : Nat)
    (s : Nat → S.Carrier) :
    SequenceEqAt S n s s := by
  exact ⟨0, fun k hk => S.eqAt_refl n (s k)⟩

@[symm] theorem sequenceEqAt_symm
    (S : Space.{u}) (n : Nat)
    {s t : Nat → S.Carrier} :
    SequenceEqAt S n s t →
      SequenceEqAt S n t s := by
  rintro ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact S.eqAt_symm n (hN k hk)

theorem sequenceEqAt_trans
    (S : Space.{u}) (n : Nat)
    {r s t : Nat → S.Carrier} :
    SequenceEqAt S n r s →
      SequenceEqAt S n s t →
        SequenceEqAt S n r t := by
  rintro ⟨Nr, hr⟩ ⟨Ns, hs⟩
  refine ⟨Nat.max Nr Ns, ?_⟩
  intro k hk
  exact S.eqAt_trans n
    (hr k (Nat.le_trans (Nat.le_max_left Nr Ns) hk))
    (hs k (Nat.le_trans (Nat.le_max_right Nr Ns) hk))

/-- The sequence filtration is descending. -/
theorem sequenceEqAt_antitone
    (S : Space.{u})
    {n m : Nat} (hnm : n ≤ m)
    {s t : Nat → S.Carrier} :
    SequenceEqAt S m s t →
      SequenceEqAt S n s t := by
  rintro ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact S.eqAt_antitone hnm (hN k hk)

@[refl] theorem sequenceEq_refl
    (S : Space.{u})
    (s : Nat → S.Carrier) :
    SequenceEq S s s := by
  intro n
  exact sequenceEqAt_refl S n s

@[symm] theorem sequenceEq_symm
    (S : Space.{u})
    {s t : Nat → S.Carrier} :
    SequenceEq S s t → SequenceEq S t s := by
  intro hst n
  exact sequenceEqAt_symm S n (hst n)

theorem sequenceEq_trans
    (S : Space.{u})
    {r s t : Nat → S.Carrier} :
    SequenceEq S r s →
      SequenceEq S s t →
        SequenceEq S r t := by
  intro hrs hst n
  exact sequenceEqAt_trans S n (hrs n) (hst n)

/-- Constant sequences converge. -/
theorem converges_const
    (S : Space.{u}) (x : S.Carrier) :
    Converges S (fun _ => x) x := by
  intro n
  exact ⟨0, fun k hk => S.eqAt_refl n x⟩

/-- Constant sequences are Cauchy. -/
theorem cauchy_const
    (S : Space.{u}) (x : S.Carrier) :
    Cauchy S (fun _ => x) := by
  intro n
  exact ⟨0, fun i j hi hj => S.eqAt_refl n x⟩

/-- Every convergent filtered sequence is Cauchy. -/
theorem converges_implies_cauchy
    (S : Space.{u})
    {s : Nat → S.Carrier}
    {x : S.Carrier}
    (hs : Converges S s x) :
    Cauchy S s := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact S.eqAt_trans n
    (S.eqAt_symm n (hN i hi))
    (hN j hj)

/-- Limits are unique because the filtration is separated. -/
theorem converges_unique
    (S : Space.{u})
    {s : Nat → S.Carrier}
    {x y : S.Carrier}
    (hx : Converges S s x)
    (hy : Converges S s y) :
    x = y := by
  apply S.separated
  intro n
  rcases hx n with ⟨Nx, hxN⟩
  rcases hy n with ⟨Ny, hyN⟩
  let k := Nat.max Nx Ny
  exact S.eqAt_trans n
    (hxN k (Nat.le_max_left Nx Ny))
    (S.eqAt_symm n (hyN k (Nat.le_max_right Nx Ny)))

/-- Convergence is asymptotic agreement with the constant limit sequence. -/
theorem converges_iff_sequenceEq_const
    (S : Space.{u})
    (s : Nat → S.Carrier)
    (x : S.Carrier) :
    Converges S s x ↔
      SequenceEq S s (fun _ => x) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact S.eqAt_symm n (hN k hk)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact S.eqAt_symm n (hN k hk)

end Filtered

namespace External

variable {Sigma : Signature.{u}}

/-- The finite observational filtration of generated Answers, viewed through
    the syntax-independent generic filtered-space interface. -/
def generatedFilteredSpace
    (D : PartialAlg.{u,v} Sigma) : Filtered.Space.{max u v} where
  Carrier := Free.GeneratedAns D
  eqAt := FiniteObservationBall D
  eqAt_refl := finiteObservationBall_center D
  eqAt_symm := finiteTagEqAt_symm D
  eqAt_trans := finiteTagEqAt_trans D
  eqAt_antitone := finiteTagEqAt_antitone D
  separated := by
    intro x y hall
    exact (all_finiteObservationBalls_iff_eq D x y).1 hall

@[simp] theorem generatedFilteredSpace_eqAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat) (x y : Free.GeneratedAns D) :
    (generatedFilteredSpace D).eqAt n x y ↔
      FiniteObservationBall D n x y := by
  rfl

/-- The abstract and specialized convergence notions are definitionally the
    same. -/
theorem filteredConverges_iff_observationalConverges
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D)
    (x : Free.GeneratedAns D) :
    Filtered.Converges (generatedFilteredSpace D) s x ↔
      ObservationalConverges D s x := by
  rfl

/-- The abstract and specialized Cauchy notions are definitionally the same. -/
theorem filteredCauchy_iff_observationalCauchy
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Free.GeneratedAns D) :
    Filtered.Cauchy (generatedFilteredSpace D) s ↔
      ObservationalCauchy D s := by
  rfl

/-- Fixed-stage sequence agreement specializes to the previous completion
    relation on representatives. -/
theorem filteredSequenceEqAt_iff_observationalSequenceEqAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (s t : Nat → Free.GeneratedAns D) :
    Filtered.SequenceEqAt (generatedFilteredSpace D) n s t ↔
      ObservationalSequenceEqAt D n s t := by
  rfl

/-- Full generic asymptotic agreement specializes to the previous quotient
    relation. -/
theorem filteredSequenceEq_iff_observationalSequenceEq
    (D : PartialAlg.{u,v} Sigma)
    (s t : Nat → Free.GeneratedAns D) :
    Filtered.SequenceEq (generatedFilteredSpace D) s t ↔
      ObservationalSequenceEq D s t := by
  rfl
end External

namespace Filtered

/-- A complete filtered space is one in which every filtered Cauchy sequence
    converges. -/
def Complete (S : Space.{u}) : Prop :=
  ∀ s : Nat → S.Carrier,
    Cauchy S s → ∃ x : S.Carrier, Converges S s x

/-- Packaged Cauchy representatives for the abstract completion. -/
structure CauchySeq (S : Space.{u}) where
  term : Nat → S.Carrier
  cauchy : Cauchy S term

/-- Asymptotic agreement is a setoid on filtered Cauchy representatives. -/
def cauchySetoid (S : Space.{u}) : Setoid (CauchySeq S) where
  r a b := SequenceEq S a.term b.term
  iseqv := by
    constructor
    · intro a
      exact sequenceEq_refl S a.term
    · intro a b hab
      exact sequenceEq_symm S hab
    · intro a b c hab hbc
      exact sequenceEq_trans S hab hbc

/-- Abstract Cauchy completion of a separated filtered space. -/
def Completion (S : Space.{u}) := Quotient (cauchySetoid S)

/-- Constant Cauchy representative of an original point. -/
def constantCauchySeq
    (S : Space.{u}) (x : S.Carrier) : CauchySeq S where
  term := fun _ => x
  cauchy := cauchy_const S x

/-- Quotient class of a Cauchy representative. -/
def classOf
    (S : Space.{u}) (s : CauchySeq S) : Completion S :=
  Quotient.mk (cauchySetoid S) s

/-- Canonical embedding into the filtered completion. -/
def embed
    (S : Space.{u}) (x : S.Carrier) : Completion S :=
  classOf S (constantCauchySeq S x)

/-- Equality of represented completion points is exactly asymptotic agreement
    of representatives. -/
theorem classOf_eq_iff
    (S : Space.{u}) (s t : CauchySeq S) :
    classOf S s = classOf S t ↔
      SequenceEq S s.term t.term := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- The canonical embedding is injective. -/
theorem embed_injective
    (S : Space.{u}) : Function.Injective (embed S) := by
  intro x y hxy
  have hrel : SequenceEq S (fun _ => x) (fun _ => y) := by
    exact Quotient.exact hxy
  apply S.separated
  intro n
  rcases hrel n with ⟨N, hN⟩
  exact hN N (Nat.le_refl N)

/-- A represented completion point equals an embedded original point exactly
    when its representative converges to that point. -/
theorem classOf_eq_embed_iff
    (S : Space.{u})
    (s : CauchySeq S) (x : S.Carrier) :
    classOf S s = embed S x ↔ Converges S s.term x := by
  change classOf S s = classOf S (constantCauchySeq S x) ↔
    Converges S s.term x
  rw [classOf_eq_iff]
  simpa [constantCauchySeq] using
    (converges_iff_sequenceEq_const S s.term x).symm

/-- Replacing either sequence by an asymptotically equivalent representative
    preserves fixed-stage eventual agreement. -/
theorem sequenceEqAt_congr
    (S : Space.{u}) (n : Nat)
    {s s' t t' : Nat → S.Carrier}
    (hss : SequenceEq S s s')
    (htt : SequenceEq S t t') :
    SequenceEqAt S n s t ↔ SequenceEqAt S n s' t' := by
  have hssn : SequenceEqAt S n s s' := hss n
  have httn : SequenceEqAt S n t t' := htt n
  constructor
  · intro hst
    exact sequenceEqAt_trans S n
      (sequenceEqAt_symm S n hssn)
      (sequenceEqAt_trans S n hst httn)
  · intro hst
    exact sequenceEqAt_trans S n hssn
      (sequenceEqAt_trans S n hst
        (sequenceEqAt_symm S n httn))

/-- Finite-stage agreement descends to completion classes. -/
def CompletionEqAt
    (S : Space.{u}) (n : Nat)
    (x y : Completion S) : Prop :=
  Quotient.liftOn₂ x y
    (fun s t => SequenceEqAt S n s.term t.term)
    (by
      intro a b a' b' haa hbb
      change SequenceEq S a.term a'.term at haa
      change SequenceEq S b.term b'.term at hbb
      apply propext
      exact sequenceEqAt_congr S n haa hbb)

@[refl] theorem completionEqAt_refl
    (S : Space.{u}) (n : Nat) (x : Completion S) :
    CompletionEqAt S n x x := by
  refine Quotient.inductionOn x ?_
  intro s
  exact sequenceEqAt_refl S n s.term

@[symm] theorem completionEqAt_symm
    (S : Space.{u}) (n : Nat)
    {x y : Completion S} :
    CompletionEqAt S n x y → CompletionEqAt S n y x := by
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  exact sequenceEqAt_symm S n hst

theorem completionEqAt_trans
    (S : Space.{u}) (n : Nat)
    {x y z : Completion S} :
    CompletionEqAt S n x y →
      CompletionEqAt S n y z →
        CompletionEqAt S n x z := by
  refine Quotient.inductionOn x ?_
  intro r
  refine Quotient.inductionOn y ?_
  intro s
  refine Quotient.inductionOn z ?_
  intro t hrs hst
  exact sequenceEqAt_trans S n hrs hst

/-- The completion-stage filtration remains descending. -/
theorem completionEqAt_antitone
    (S : Space.{u})
    {n m : Nat} (hnm : n ≤ m)
    {x y : Completion S} :
    CompletionEqAt S m x y → CompletionEqAt S n x y := by
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  exact sequenceEqAt_antitone S hnm hst

/-- The embedding preserves and reflects every finite stage. -/
theorem completionEqAt_embed_iff
    (S : Space.{u}) (n : Nat)
    (x y : S.Carrier) :
    CompletionEqAt S n (embed S x) (embed S y) ↔
      S.eqAt n x y := by
  change SequenceEqAt S n (fun _ => x) (fun _ => y) ↔
    S.eqAt n x y
  constructor
  · rintro ⟨N, hN⟩
    exact hN N (Nat.le_refl N)
  · intro hxy
    exact ⟨0, fun k hk => hxy⟩

/-- Completion classes are separated by the completed finite stages. -/
theorem forall_completionEqAt_iff_eq
    (S : Space.{u}) (x y : Completion S) :
    (∀ n : Nat, CompletionEqAt S n x y) ↔ x = y := by
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t
  constructor
  · intro hall
    apply Quotient.sound
    change SequenceEq S s.term t.term
    intro n
    exact hall n
  · intro hxy
    have hrel := Quotient.exact hxy
    change SequenceEq S s.term t.term at hrel
    exact hrel

/-- The quotient completion itself carries the canonical separated filtered
    structure. -/
def completionSpace (S : Space.{u}) : Space.{u} where
  Carrier := Completion S
  eqAt := CompletionEqAt S
  eqAt_refl := completionEqAt_refl S
  eqAt_symm := completionEqAt_symm S
  eqAt_trans := completionEqAt_trans S
  eqAt_antitone := completionEqAt_antitone S
  separated := by
    intro x y hall
    exact (forall_completionEqAt_iff_eq S x y).1 hall

/-- At every finite stage, embedded original points are dense in the
    completion. -/
theorem embed_stage_dense
    (S : Space.{u}) (n : Nat) (q : Completion S) :
    ∃ x : S.Carrier, CompletionEqAt S n q (embed S x) := by
  refine Quotient.inductionOn q ?_
  intro s
  rcases s.cauchy n with ⟨N, hN⟩
  refine ⟨s.term N, ?_⟩
  change SequenceEqAt S n s.term (fun _ => s.term N)
  exact ⟨N, fun k hk => hN k N hk (Nat.le_refl N)⟩

/-- Convergence and Cauchy behavior on the completion are simply the generic
    notions for `completionSpace`. -/
abbrev CompletionConverges
    (S : Space.{u})
    (s : Nat → Completion S) (x : Completion S) : Prop :=
  Converges (completionSpace S) s x

abbrev CompletionCauchy
    (S : Space.{u})
    (s : Nat → Completion S) : Prop :=
  Cauchy (completionSpace S) s

/-- Completion limits are unique. -/
theorem completionConverges_unique
    (S : Space.{u})
    {s : Nat → Completion S}
    {x y : Completion S}
    (hx : CompletionConverges S s x)
    (hy : CompletionConverges S s y) : x = y :=
  converges_unique (completionSpace S) hx hy

/-- At stage `k`, choose an original point approximating the `k`th completion
    point through stage `k`. -/
noncomputable def approximation
    (S : Space.{u})
    (q : Nat → Completion S) (k : Nat) : S.Carrier :=
  Classical.choose (embed_stage_dense S k (q k))

theorem approximation_spec
    (S : Space.{u})
    (q : Nat → Completion S) (k : Nat) :
    CompletionEqAt S k (q k) (embed S (approximation S q k)) :=
  Classical.choose_spec (embed_stage_dense S k (q k))

/-- Diagonal finite-stage approximants of a Cauchy completion sequence form an
    original filtered Cauchy sequence. -/
theorem approximation_cauchy
    (S : Space.{u})
    {q : Nat → Completion S}
    (hq : CompletionCauchy S q) :
    Cauchy S (fun k => approximation S q k) := by
  intro n
  rcases hq n with ⟨N, hN⟩
  refine ⟨Nat.max N n, ?_⟩
  intro i j hi hj
  have hNi : N ≤ i :=
    Nat.le_trans (Nat.le_max_left N n) hi
  have hNj : N ≤ j :=
    Nat.le_trans (Nat.le_max_left N n) hj
  have hni : n ≤ i :=
    Nat.le_trans (Nat.le_max_right N n) hi
  have hnj : n ≤ j :=
    Nat.le_trans (Nat.le_max_right N n) hj
  have hiApprox :
      CompletionEqAt S n (q i) (embed S (approximation S q i)) :=
    completionEqAt_antitone S hni (approximation_spec S q i)
  have hjApprox :
      CompletionEqAt S n (q j) (embed S (approximation S q j)) :=
    completionEqAt_antitone S hnj (approximation_spec S q j)
  have hij :
      CompletionEqAt S n
        (embed S (approximation S q i))
        (embed S (approximation S q j)) :=
    completionEqAt_trans S n
      (completionEqAt_symm S n hiApprox)
      (completionEqAt_trans S n (hN i j hNi hNj) hjApprox)
  exact (completionEqAt_embed_iff S n
    (approximation S q i) (approximation S q j)).1 hij

/-- Packaged diagonal representative. -/
noncomputable def diagonalSeq
    (S : Space.{u})
    (q : Nat → Completion S)
    (hq : CompletionCauchy S q) : CauchySeq S where
  term := fun k => approximation S q k
  cauchy := approximation_cauchy S hq

/-- Canonical diagonal limit of a Cauchy sequence of completion points. -/
noncomputable def completionLimit
    (S : Space.{u})
    (q : Nat → Completion S)
    (hq : CompletionCauchy S q) : Completion S :=
  classOf S (diagonalSeq S q hq)

/-- A represented class and an embedded point agree at stage `n` exactly when
    the representative sequence is eventually related to the constant point. -/
theorem completionEqAt_class_embed_iff
    (S : Space.{u}) (n : Nat)
    (s : CauchySeq S) (x : S.Carrier) :
    CompletionEqAt S n (classOf S s) (embed S x) ↔
      SequenceEqAt S n s.term (fun _ => x) := by
  rfl

/-- The diagonal class is a limit of the original completion-valued Cauchy
    sequence. -/
theorem completionConverges_to_limit
    (S : Space.{u})
    {q : Nat → Completion S}
    (hq : CompletionCauchy S q) :
    CompletionConverges S q (completionLimit S q hq) := by
  intro n
  have ha : Cauchy S (fun k => approximation S q k) :=
    approximation_cauchy S hq
  rcases ha n with ⟨M, hM⟩
  refine ⟨Nat.max M n, ?_⟩
  intro k hk
  have hMk : M ≤ k :=
    Nat.le_trans (Nat.le_max_left M n) hk
  have hnk : n ≤ k :=
    Nat.le_trans (Nat.le_max_right M n) hk
  have hclassEmbed :
      CompletionEqAt S n
        (completionLimit S q hq)
        (embed S (approximation S q k)) := by
    apply (completionEqAt_class_embed_iff S n
      (diagonalSeq S q hq) (approximation S q k)).2
    change SequenceEqAt S n
      (fun j => approximation S q j)
      (fun _ => approximation S q k)
    exact ⟨M, fun j hj => hM j k hj hMk⟩
  have hqEmbed :
      CompletionEqAt S n (q k)
        (embed S (approximation S q k)) :=
    completionEqAt_antitone S hnk (approximation_spec S q k)
  exact completionEqAt_trans S n hclassEmbed
    (completionEqAt_symm S n hqEmbed)

/-- The abstract Cauchy quotient is complete. -/
theorem completionSpace_is_complete
    (S : Space.{u}) : Complete (completionSpace S) := by
  intro q hq
  exact ⟨completionLimit S q hq,
    completionConverges_to_limit S hq⟩

end Filtered

namespace External

variable {Sigma : Signature.{u}}
/-- Convert a generic filtered Cauchy representative of generated Answers to
    the original observational representative type. -/
def filteredToObservationalCauchySeq
    (D : PartialAlg.{u,v} Sigma)
    (s : Filtered.CauchySeq (generatedFilteredSpace D)) :
    ObservationalCauchySeq D where
  term := s.term
  cauchy := s.cauchy

/-- Convert an observational Cauchy representative to the generic filtered
    representative type. -/
def observationalToFilteredCauchySeq
    (D : PartialAlg.{u,v} Sigma)
    (s : ObservationalCauchySeq D) :
    Filtered.CauchySeq (generatedFilteredSpace D) where
  term := s.term
  cauchy := s.cauchy

/-- Canonical map from the abstract filtered completion to the previously
    constructed observational completion. -/
def filteredCompletionToObservational
    (D : PartialAlg.{u,v} Sigma)
    (q : Filtered.Completion (generatedFilteredSpace D)) :
    ObservationalCompletion D :=
  Quotient.liftOn q
    (fun s => observationalCompletionClass D
      (filteredToObservationalCauchySeq D s))
    (by
      intro s t hst
      apply Quotient.sound
      change Filtered.SequenceEq (generatedFilteredSpace D)
        s.term t.term at hst
      change ObservationalSequenceEq D s.term t.term
      exact hst)

/-- Canonical map from the observational completion back to the abstract
    filtered completion. -/
def observationalCompletionToFiltered
    (D : PartialAlg.{u,v} Sigma)
    (q : ObservationalCompletion D) :
    Filtered.Completion (generatedFilteredSpace D) :=
  Quotient.liftOn q
    (fun s => Filtered.classOf (generatedFilteredSpace D)
      (observationalToFilteredCauchySeq D s))
    (by
      intro s t hst
      apply Quotient.sound
      change ObservationalSequenceEq D s.term t.term at hst
      change Filtered.SequenceEq (generatedFilteredSpace D)
        s.term t.term
      exact hst)

/-- Converting a generic completion point to the observational completion and
    back is the identity. -/
theorem observationalToFiltered_after_filteredToObservational
    (D : PartialAlg.{u,v} Sigma)
    (q : Filtered.Completion (generatedFilteredSpace D)) :
    observationalCompletionToFiltered D
        (filteredCompletionToObservational D q) = q := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  change Filtered.SequenceEq (generatedFilteredSpace D)
    s.term s.term
  exact Filtered.sequenceEq_refl (generatedFilteredSpace D) s.term

/-- Converting an observational completion point to the generic completion and
    back is the identity. -/
theorem filteredToObservational_after_observationalToFiltered
    (D : PartialAlg.{u,v} Sigma)
    (q : ObservationalCompletion D) :
    filteredCompletionToObservational D
        (observationalCompletionToFiltered D q) = q := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  change ObservationalSequenceEq D s.term s.term
  exact observationalSequenceEq_refl D s.term

/-- The comparison map sends the generic embedding to the observational
    embedding. -/
theorem filteredCompletionToObservational_embed
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    filteredCompletionToObservational D
        (Filtered.embed (generatedFilteredSpace D) x) =
      observationalCompletionEmbed D x := by
  apply Quotient.sound
  change ObservationalSequenceEq D (fun _ => x) (fun _ => x)
  exact observationalSequenceEq_refl D (fun _ => x)

/-- The inverse comparison map also preserves the canonical embedding. -/
theorem observationalCompletionToFiltered_embed
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    observationalCompletionToFiltered D
        (observationalCompletionEmbed D x) =
      Filtered.embed (generatedFilteredSpace D) x := by
  apply Quotient.sound
  change Filtered.SequenceEq (generatedFilteredSpace D)
    (fun _ => x) (fun _ => x)
  exact Filtered.sequenceEq_refl
    (generatedFilteredSpace D) (fun _ => x)

/-- The comparison maps preserve and reflect every completed finite stage. -/
theorem filteredCompletionEqAt_iff_observationalCompletionEqAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (q r : Filtered.Completion (generatedFilteredSpace D)) :
    Filtered.CompletionEqAt (generatedFilteredSpace D) n q r ↔
      CompletionEqAt D n
        (filteredCompletionToObservational D q)
        (filteredCompletionToObservational D r) := by
  refine Quotient.inductionOn q ?_
  intro s
  refine Quotient.inductionOn r ?_
  intro t
  rfl

/-- The inverse comparison maps preserve and reflect every completed finite
    stage as well. -/
theorem observationalCompletionEqAt_iff_filteredCompletionEqAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (q r : ObservationalCompletion D) :
    CompletionEqAt D n q r ↔
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (observationalCompletionToFiltered D q)
        (observationalCompletionToFiltered D r) := by
  refine Quotient.inductionOn q ?_
  intro s
  refine Quotient.inductionOn r ?_
  intro t
  rfl

/-- Completion convergence is transported exactly by the comparison map. -/
theorem filteredCompletionConverges_iff_observationalCompletionConverges
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Filtered.Completion (generatedFilteredSpace D))
    (q : Filtered.Completion (generatedFilteredSpace D)) :
    Filtered.CompletionConverges (generatedFilteredSpace D) s q ↔
      CompletionConverges D
        (fun k => filteredCompletionToObservational D (s k))
        (filteredCompletionToObservational D q) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (filteredCompletionEqAt_iff_observationalCompletionEqAt
      D n q (s k)).1 (hN k hk)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    exact (filteredCompletionEqAt_iff_observationalCompletionEqAt
      D n q (s k)).2 (hN k hk)

/-- Completion Cauchy behavior is also transported exactly. -/
theorem filteredCompletionCauchy_iff_observationalCompletionCauchy
    (D : PartialAlg.{u,v} Sigma)
    (s : Nat → Filtered.Completion (generatedFilteredSpace D)) :
    Filtered.CompletionCauchy (generatedFilteredSpace D) s ↔
      CompletionCauchy D
        (fun k => filteredCompletionToObservational D (s k)) := by
  constructor
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro i j hi hj
    exact (filteredCompletionEqAt_iff_observationalCompletionEqAt
      D n (s i) (s j)).1 (hN i j hi hj)
  · intro hs n
    rcases hs n with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro i j hi hj
    exact (filteredCompletionEqAt_iff_observationalCompletionEqAt
      D n (s i) (s j)).2 (hN i j hi hj)

/-- The earlier observational completion is therefore precisely the abstract
    filtered completion, up to mutually inverse stage-preserving maps. -/
theorem observationalCompletion_is_generic_filtered_completion
    (D : PartialAlg.{u,v} Sigma) :
    (∀ q : Filtered.Completion (generatedFilteredSpace D),
      observationalCompletionToFiltered D
        (filteredCompletionToObservational D q) = q) ∧
    (∀ q : ObservationalCompletion D,
      filteredCompletionToObservational D
        (observationalCompletionToFiltered D q) = q) := by
  constructor
  · exact observationalToFiltered_after_filteredToObservational D
  · exact filteredToObservational_after_observationalToFiltered D
end External

namespace Filtered

/-- Morphisms of filtered spaces preserve every finite-stage equivalence. -/
structure Nonexpansive
    (S : Space.{u}) (T : Space.{v}) where
  toFun : S.Carrier → T.Carrier
  map_eqAt : ∀ n : Nat, ∀ {x y : S.Carrier},
    S.eqAt n x y → T.eqAt n (toFun x) (toFun y)

/-- A nonexpansive map sends Cauchy sequences to Cauchy sequences. -/
theorem Nonexpansive.map_cauchy
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    {s : Nat → S.Carrier}
    (hs : Cauchy S s) :
    Cauchy T (fun k => f.toFun (s k)) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact f.map_eqAt n (hN i j hi hj)

/-- Pointwise application preserves full asymptotic sequence agreement. -/
theorem Nonexpansive.map_sequenceEq
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    {s t : Nat → S.Carrier}
    (hst : SequenceEq S s t) :
    SequenceEq T
      (fun k => f.toFun (s k))
      (fun k => f.toFun (t k)) := by
  intro n
  rcases hst n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact f.map_eqAt n (hN k hk)

/-- Pointwise application preserves one fixed asymptotic stage. -/
theorem Nonexpansive.map_sequenceEqAt
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (n : Nat)
    {s t : Nat → S.Carrier}
    (hst : SequenceEqAt S n s t) :
    SequenceEqAt T n
      (fun k => f.toFun (s k))
      (fun k => f.toFun (t k)) := by
  rcases hst with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact f.map_eqAt n (hN k hk)

/-- Pointwise image of a packaged Cauchy representative. -/
def mapCauchySeq
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (s : CauchySeq S) : CauchySeq T where
  term := fun k => f.toFun (s.term k)
  cauchy := f.map_cauchy s.cauchy

/-- Every nonexpansive filtered map extends canonically to the quotient
    completions by pointwise action on representatives. -/
def completionMap
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (q : Completion S) : Completion T :=
  Quotient.liftOn q
    (fun s => classOf T (mapCauchySeq f s))
    (by
      intro s t hst
      apply Quotient.sound
      change SequenceEq S s.term t.term at hst
      exact f.map_sequenceEq hst)

/-- The completion extension agrees with the original map on embedded points. -/
theorem completionMap_embed
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (x : S.Carrier) :
    completionMap f (embed S x) = embed T (f.toFun x) := by
  apply Quotient.sound
  exact sequenceEq_refl T (fun _ => f.toFun x)

/-- Completion extensions preserve every completed finite stage. -/
theorem completionMap_preserves_eqAt
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (n : Nat)
    {x y : Completion S}
    (hxy : CompletionEqAt S n x y) :
    CompletionEqAt T n (completionMap f x) (completionMap f y) := by
  revert hxy
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t hst
  change SequenceEqAt S n s.term t.term at hst
  change SequenceEqAt T n
    (fun k => f.toFun (s.term k))
    (fun k => f.toFun (t.term k))
  exact f.map_sequenceEqAt n hst

/-- Completion extensions preserve convergent completion-valued sequences. -/
theorem completionMap_preserves_convergence
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    {s : Nat → Completion S}
    {x : Completion S}
    (hs : CompletionConverges S s x) :
    CompletionConverges T
      (fun k => completionMap f (s k))
      (completionMap f x) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact completionMap_preserves_eqAt f n (hN k hk)

/-- Completion extensions preserve completion-valued Cauchy sequences. -/
theorem completionMap_preserves_cauchy
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    {s : Nat → Completion S}
    (hs : CompletionCauchy S s) :
    CompletionCauchy T (fun k => completionMap f (s k)) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hj
  exact completionMap_preserves_eqAt f n (hN i j hi hj)

/-- Identity filtered morphism. -/
def Nonexpansive.id (S : Space.{u}) : Nonexpansive S S where
  toFun := fun x => x
  map_eqAt := by
    intro n x y hxy
    exact hxy

/-- Composition of filtered morphisms. -/
def Nonexpansive.comp
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (g : Nonexpansive T U)
    (f : Nonexpansive S T) : Nonexpansive S U where
  toFun := fun x => g.toFun (f.toFun x)
  map_eqAt := by
    intro n x y hxy
    exact g.map_eqAt n (f.map_eqAt n hxy)

/-- Completion sends the identity to the identity. -/
theorem completionMap_id
    (S : Space.{u}) (q : Completion S) :
    completionMap (Nonexpansive.id S) q = q := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  exact sequenceEq_refl S s.term

/-- Completion respects composition. -/
theorem completionMap_comp
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (g : Nonexpansive T U)
    (f : Nonexpansive S T)
    (q : Completion S) :
    completionMap (Nonexpansive.comp g f) q =
      completionMap g (completionMap f q) := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  exact sequenceEq_refl U
    (fun k => g.toFun (f.toFun (s.term k)))

/-- The canonical embedding is itself a nonexpansive filtered morphism. -/
def completionUnit (S : Space.{u}) :
    Nonexpansive S (completionSpace S) where
  toFun := embed S
  map_eqAt := by
    intro n x y hxy
    exact (completionEqAt_embed_iff S n x y).2 hxy

/-- Naturality of the completion unit. -/
theorem completionUnit_natural
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (x : S.Carrier) :
    completionMap f ((completionUnit S).toFun x) =
      (completionUnit T).toFun (f.toFun x) :=
  completionMap_embed f x

end Filtered

namespace External

variable {Sigma : Signature.{u}}
end External

namespace Filtered

/-- Nonexpansive maps preserve convergence. -/
theorem Nonexpansive.map_converges
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    {s : Nat → S.Carrier}
    {x : S.Carrier}
    (hs : Converges S s x) :
    Converges T (fun k => f.toFun (s k)) (f.toFun x) := by
  intro n
  rcases hs n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact f.map_eqAt n (hN k hk)

/-- Every Cauchy representative converges, after embedding its terms, to its
    own completion class. -/
theorem embed_sequence_converges
    (S : Space.{u})
    (s : CauchySeq S) :
    CompletionConverges S
      (fun k => embed S (s.term k))
      (classOf S s) := by
  intro n
  rcases s.cauchy n with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  apply (completionEqAt_class_embed_iff S n s (s.term k)).2
  exact ⟨N, fun j hj => hN j k hj hk⟩

/-- The original filtered space is sequentially dense in its completion. -/
theorem embed_sequentially_dense
    (S : Space.{u})
    (q : Completion S) :
    ∃ s : CauchySeq S,
      CompletionConverges S
        (fun k => embed S (s.term k)) q := by
  refine Quotient.inductionOn q ?_
  intro s
  exact ⟨s, embed_sequence_converges S s⟩

/-- Completeness of the original space makes its canonical completion embedding
    surjective. -/
theorem complete_implies_embed_surjective
    (S : Space.{u})
    (hS : Complete S) :
    Function.Surjective (embed S) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro s
  change ∃ x : S.Carrier, embed S x = classOf S s
  rcases hS s.term s.cauchy with ⟨x, hx⟩
  exact ⟨x, ((classOf_eq_embed_iff S s x).2 hx).symm⟩

/-- Conversely, surjectivity of the canonical embedding forces every Cauchy
    sequence to converge. -/
theorem embed_surjective_implies_complete
    (S : Space.{u})
    (hSurj : Function.Surjective (embed S)) :
    Complete S := by
  intro t ht
  let s : CauchySeq S := { term := t, cauchy := ht }
  rcases hSurj (classOf S s) with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hclass : classOf S s = embed S x := hx.symm
  have hconv := (classOf_eq_embed_iff S s x).1 hclass
  simpa [s] using hconv

/-- A separated filtered space is complete exactly when the canonical
    completion embedding is surjective. -/
theorem complete_iff_embed_surjective
    (S : Space.{u}) :
    Complete S ↔ Function.Surjective (embed S) := by
  constructor
  · exact complete_implies_embed_surjective S
  · exact embed_surjective_implies_complete S

/-- Since the completion embedding is always injective, completeness is also
    equivalent to explicit inverse data. -/
theorem complete_iff_embed_inverse_data
    (S : Space.{u}) :
    Complete S ↔
      Function.Injective (embed S) ∧ Function.Surjective (embed S) := by
  constructor
  · intro hS
    exact ⟨embed_injective S, complete_implies_embed_surjective S hS⟩
  · intro hData
    exact embed_surjective_implies_complete S hData.2

/-- Under completeness, choose the unique original point represented by a
    completion point. -/
noncomputable def completionInverse
    (S : Space.{u})
    (hS : Complete S)
    (q : Completion S) : S.Carrier :=
  Classical.choose (complete_implies_embed_surjective S hS q)

/-- Embedding after the chosen inverse returns the original completion point. -/
theorem embed_inverse_right
    (S : Space.{u})
    (hS : Complete S)
    (q : Completion S) :
    embed S (completionInverse S hS q) = q :=
  Classical.choose_spec (complete_implies_embed_surjective S hS q)

/-- The chosen inverse after embedding returns the original point. -/
theorem embed_inverse_left
    (S : Space.{u})
    (hS : Complete S)
    (x : S.Carrier) :
    completionInverse S hS (embed S x) = x := by
  apply embed_injective S
  exact embed_inverse_right S hS (embed S x)

/-- Under completeness, the chosen inverse transports every completed finite
    stage exactly back to the original filtered space. -/
theorem completionInverse_eqAt_iff
    (S : Space.{u})
    (hS : Complete S)
    (n : Nat)
    (q r : Completion S) :
    CompletionEqAt S n q r ↔
      S.eqAt n
        (completionInverse S hS q)
        (completionInverse S hS r) := by
  have h := completionEqAt_embed_iff S n
    (completionInverse S hS q)
    (completionInverse S hS r)
  rw [embed_inverse_right S hS q,
    embed_inverse_right S hS r] at h
  exact h

/-- The chosen inverse is nonexpansive. -/
noncomputable def completionInverseNonexpansive
    (S : Space.{u})
    (hS : Complete S) :
    Nonexpansive (completionSpace S) S where
  toFun := completionInverse S hS
  map_eqAt := by
    intro n q r hqr
    exact (completionInverse_eqAt_iff S hS n q r).1 hqr

/-- Canonical extension of a filtered morphism into a complete target. -/
noncomputable def completeExtension
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T)
    (q : Completion S) : T.Carrier :=
  completionInverse T hT (completionMap f q)

/-- The complete-target extension agrees with the original map on embedded
    points. -/
theorem completeExtension_embed
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T)
    (x : S.Carrier) :
    completeExtension f hT (embed S x) = f.toFun x := by
  unfold completeExtension
  rw [completionMap_embed]
  exact embed_inverse_left T hT (f.toFun x)

/-- The complete-target extension preserves every completed finite stage. -/
theorem completeExtension_preserves_eqAt
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T)
    (n : Nat)
    {q r : Completion S}
    (hqr : CompletionEqAt S n q r) :
    T.eqAt n
      (completeExtension f hT q)
      (completeExtension f hT r) := by
  apply (completionInverse_eqAt_iff T hT n
    (completionMap f q) (completionMap f r)).1
  exact completionMap_preserves_eqAt f n hqr

/-- The canonical complete-target extension, packaged as a filtered morphism. -/
noncomputable def completeExtensionNonexpansive
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T) :
    Nonexpansive (completionSpace S) T where
  toFun := completeExtension f hT
  map_eqAt := by
    intro n q r hqr
    exact completeExtension_preserves_eqAt f hT n hqr

/-- The complete-target extension preserves convergence. -/
theorem completeExtension_preserves_convergence
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T)
    {s : Nat → Completion S}
    {q : Completion S}
    (hs : CompletionConverges S s q) :
    Converges T
      (fun k => completeExtension f hT (s k))
      (completeExtension f hT q) :=
  (completeExtensionNonexpansive f hT).map_converges hs

/-- Universal uniqueness: any nonexpansive map out of the completion that
    agrees with `f` on embedded points is the canonical extension. -/
theorem completeExtension_unique
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T)
    (g : Nonexpansive (completionSpace S) T)
    (hgEmbed : ∀ x : S.Carrier,
      g.toFun (embed S x) = f.toFun x) :
    g.toFun = completeExtension f hT := by
  funext q
  rcases embed_sequentially_dense S q with ⟨s, hs⟩
  have hgConv :
      Converges T
        (fun k => g.toFun (embed S (s.term k)))
        (g.toFun q) :=
    g.map_converges hs
  have hExtConv :
      Converges T
        (fun k => completeExtension f hT (embed S (s.term k)))
        (completeExtension f hT q) :=
    completeExtension_preserves_convergence f hT hs
  have hSeq :
      (fun k => g.toFun (embed S (s.term k))) =
        (fun k => completeExtension f hT
          (embed S (s.term k))) := by
    funext k
    calc
      g.toFun (embed S (s.term k)) = f.toFun (s.term k) :=
        hgEmbed (s.term k)
      _ = completeExtension f hT (embed S (s.term k)) :=
        (completeExtension_embed f hT (s.term k)).symm
  rw [hSeq] at hgConv
  exact converges_unique T hgConv hExtConv

/-- Reflector form of the completion universal property: the canonical
    extension exists, agrees with the source map on the unit, and is unique
    among nonexpansive extensions. -/
theorem completion_reflector_universal
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T)
    (hT : Complete T) :
    (∀ x : S.Carrier,
      (completeExtensionNonexpansive f hT).toFun (embed S x) =
        f.toFun x) ∧
    (∀ g : Nonexpansive (completionSpace S) T,
      (∀ x : S.Carrier, g.toFun (embed S x) = f.toFun x) →
        g.toFun = (completeExtensionNonexpansive f hT).toFun) := by
  constructor
  · intro x
    exact completeExtension_embed f hT x
  · intro g hg
    exact completeExtension_unique f hT g hg

/-- Isomorphism of filtered spaces, expressed by mutually inverse
    nonexpansive maps. -/
structure Iso (S : Space.{u}) (T : Space.{v}) where
  hom : Nonexpansive S T
  inv : Nonexpansive T S
  left_inv : ∀ x : S.Carrier, inv.toFun (hom.toFun x) = x
  right_inv : ∀ y : T.Carrier, hom.toFun (inv.toFun y) = y

/-- Flatten the completion of an already completed filtered space. -/
noncomputable def completionFlatten
    (S : Space.{u}) :
    Completion (completionSpace S) → Completion S :=
  completionInverse (completionSpace S) (completionSpace_is_complete S)

/-- Flattening after the second completion embedding is the identity. -/
theorem completionFlatten_secondEmbed
    (S : Space.{u})
    (q : Completion S) :
    completionFlatten S (embed (completionSpace S) q) = q :=
  embed_inverse_left (completionSpace S)
    (completionSpace_is_complete S) q

/-- The second completion embedding after flattening is the identity. -/
theorem completionSecondEmbed_flatten
    (S : Space.{u})
    (Q : Completion (completionSpace S)) :
    embed (completionSpace S) (completionFlatten S Q) = Q :=
  embed_inverse_right (completionSpace S)
    (completionSpace_is_complete S) Q

/-- Flattening is a nonexpansive morphism. -/
noncomputable def completionFlattenNonexpansive
    (S : Space.{u}) :
    Nonexpansive (completionSpace (completionSpace S))
      (completionSpace S) :=
  completionInverseNonexpansive (completionSpace S)
    (completionSpace_is_complete S)

/-- Completion is idempotent up to a canonical filtered-space isomorphism. -/
noncomputable def completionIdempotenceIso
    (S : Space.{u}) :
    Iso (completionSpace S) (completionSpace (completionSpace S)) where
  hom := completionUnit (completionSpace S)
  inv := completionFlattenNonexpansive S
  left_inv := completionFlatten_secondEmbed S
  right_inv := completionSecondEmbed_flatten S

/-- Explicit inverse laws for completion idempotence. -/
theorem completion_is_idempotent
    (S : Space.{u}) :
    (∀ q : Completion S,
      completionFlatten S (embed (completionSpace S) q) = q) ∧
    (∀ Q : Completion (completionSpace S),
      embed (completionSpace S) (completionFlatten S Q) = Q) := by
  constructor
  · exact completionFlatten_secondEmbed S
  · exact completionSecondEmbed_flatten S

end Filtered

namespace External

variable {Sigma : Signature.{u}}
end External

namespace Filtered

/-- The functorial action of completion, packaged as a nonexpansive map between
    completed filtered spaces. -/
def completionMapNonexpansive
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T) :
    Nonexpansive (completionSpace S) (completionSpace T) where
  toFun := completionMap f
  map_eqAt := by
    intro n x y hxy
    exact completionMap_preserves_eqAt f n hxy

/-- The packaged completion functor preserves identity maps at the level of
    underlying functions. -/
theorem completionFunctor_id
    (S : Space.{u}) :
    (completionMapNonexpansive (Nonexpansive.id S)).toFun =
      (Nonexpansive.id (completionSpace S)).toFun := by
  funext q
  exact completionMap_id S q

/-- The packaged completion functor preserves composition at the level of
    underlying functions. -/
theorem completionFunctor_comp
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (g : Nonexpansive T U)
    (f : Nonexpansive S T) :
    (completionMapNonexpansive (Nonexpansive.comp g f)).toFun =
      (Nonexpansive.comp
        (completionMapNonexpansive g)
        (completionMapNonexpansive f)).toFun := by
  funext q
  exact completionMap_comp g f q

/-- Applying completion to the unit agrees everywhere with the unit of the
    completed space. This upgrades pointwise unit naturality from the dense
    source to the whole completion. -/
theorem completionMap_unit_eq_secondUnit
    (S : Space.{u}) :
    (completionMapNonexpansive (completionUnit S)).toFun =
      (completionUnit (completionSpace S)).toFun := by
  let doubledUnit :
      Nonexpansive S (completionSpace (completionSpace S)) :=
    Nonexpansive.comp
      (completionUnit (completionSpace S))
      (completionUnit S)
  have hMap := completeExtension_unique doubledUnit
    (completionSpace_is_complete (completionSpace S))
    (completionMapNonexpansive (completionUnit S)) (by
      intro x
      change completionMap (completionUnit S) (embed S x) =
        embed (completionSpace S) (embed S x)
      exact completionMap_embed (completionUnit S) x)
  have hUnit := completeExtension_unique doubledUnit
    (completionSpace_is_complete (completionSpace S))
    (completionUnit (completionSpace S)) (by
      intro x
      rfl)
  exact hMap.trans hUnit.symm

/-- The second unit law in pointwise form. -/
theorem completionMap_unit_eq_secondUnit_apply
    (S : Space.{u})
    (q : Completion S) :
    completionMap (completionUnit S) q =
      embed (completionSpace S) q := by
  exact congrFun (completionMap_unit_eq_secondUnit S) q

/-- Multiplication after the functorial image of the unit is the identity. -/
theorem completionFlatten_map_unit
    (S : Space.{u})
    (q : Completion S) :
    completionFlatten S
        (completionMap (completionUnit S) q) = q := by
  rw [completionMap_unit_eq_secondUnit_apply]
  exact completionFlatten_secondEmbed S q

/-- Both unit laws for the completion multiplication. -/
theorem completion_monad_unit_laws
    (S : Space.{u}) :
    (∀ q : Completion S,
      completionFlatten S (embed (completionSpace S) q) = q) ∧
    (∀ q : Completion S,
      completionFlatten S
        (completionMap (completionUnit S) q) = q) := by
  constructor
  · exact completionFlatten_secondEmbed S
  · exact completionFlatten_map_unit S

/-- Naturality of the completion multiplication. -/
theorem completionFlatten_natural
    {S : Space.{u}} {T : Space.{v}}
    (f : Nonexpansive S T) :
    (Nonexpansive.comp
      (completionFlattenNonexpansive T)
      (completionMapNonexpansive
        (completionMapNonexpansive f))).toFun =
    (Nonexpansive.comp
      (completionMapNonexpansive f)
      (completionFlattenNonexpansive S)).toFun := by
  let completedMap :
      Nonexpansive (completionSpace S) (completionSpace T) :=
    completionMapNonexpansive f
  have hLeft := completeExtension_unique completedMap
    (completionSpace_is_complete T)
    (Nonexpansive.comp
      (completionFlattenNonexpansive T)
      (completionMapNonexpansive completedMap)) (by
      intro q
      have hMap := completionMap_embed completedMap q
      have hMapFlat := congrArg
        (completionFlattenNonexpansive T).toFun hMap
      have hUnit := (completionIdempotenceIso T).left_inv
        (completedMap.toFun q)
      simpa [Nonexpansive.comp, completionMapNonexpansive,
        completionIdempotenceIso] using hMapFlat.trans hUnit)
  have hRight := completeExtension_unique completedMap
    (completionSpace_is_complete T)
    (Nonexpansive.comp
      completedMap
      (completionFlattenNonexpansive S)) (by
      intro q
      have hUnit := (completionIdempotenceIso S).left_inv q
      change
        (completionFlattenNonexpansive S).toFun
          ((completionUnit (completionSpace S)).toFun q) = q at hUnit
      change
        completedMap.toFun
          ((completionFlattenNonexpansive S).toFun
            ((completionUnit (completionSpace S)).toFun q)) =
          completedMap.toFun q
      exact congrArg completedMap.toFun hUnit)
  simpa [completedMap] using hLeft.trans hRight.symm

/-- Associativity of completion multiplication. -/
theorem completionFlatten_associative
    (S : Space.{u}) :
    (Nonexpansive.comp
      (completionFlattenNonexpansive S)
      (completionFlattenNonexpansive
        (completionSpace S))).toFun =
    (Nonexpansive.comp
      (completionFlattenNonexpansive S)
      (completionMapNonexpansive
        (completionFlattenNonexpansive S))).toFun := by
  let flatten :
      Nonexpansive (completionSpace (completionSpace S))
        (completionSpace S) :=
    completionFlattenNonexpansive S
  have hLeft := completeExtension_unique flatten
    (completionSpace_is_complete S)
    (Nonexpansive.comp
      (completionFlattenNonexpansive S)
      (completionFlattenNonexpansive
        (completionSpace S))) (by
      intro Q
      have hUnit :=
        (completionIdempotenceIso (completionSpace S)).left_inv Q
      change
        (completionFlattenNonexpansive (completionSpace S)).toFun
          ((completionUnit
            (completionSpace (completionSpace S))).toFun Q) = Q at hUnit
      change
        (completionFlattenNonexpansive S).toFun
          ((completionFlattenNonexpansive (completionSpace S)).toFun
            ((completionUnit
              (completionSpace (completionSpace S))).toFun Q)) =
          (completionFlattenNonexpansive S).toFun Q
      exact congrArg (completionFlattenNonexpansive S).toFun hUnit)
  have hRight := completeExtension_unique flatten
    (completionSpace_is_complete S)
    (Nonexpansive.comp
      (completionFlattenNonexpansive S)
      (completionMapNonexpansive flatten)) (by
      intro Q
      have hMap := completionMap_embed flatten Q
      have hMapFlat := congrArg
        (completionFlattenNonexpansive S).toFun hMap
      have hUnit := (completionIdempotenceIso S).left_inv
        (flatten.toFun Q)
      simpa [Nonexpansive.comp, completionMapNonexpansive,
        completionIdempotenceIso] using hMapFlat.trans hUnit)
  simpa [flatten] using hLeft.trans hRight.symm

/-- The unit and multiplication satisfy the pointwise idempotent-monad laws;
    functorial identity, composition, and multiplication naturality are provided
    by the preceding theorems. -/
theorem completion_idempotent_monad_package
    (S : Space.{u}) :
    (∀ q : Completion S,
      completionFlatten S (embed (completionSpace S) q) = q) ∧
    (∀ q : Completion S,
      completionFlatten S
        (completionMap (completionUnit S) q) = q) ∧
    (Nonexpansive.comp
      (completionFlattenNonexpansive S)
      (completionFlattenNonexpansive
        (completionSpace S))).toFun =
    (Nonexpansive.comp
      (completionFlattenNonexpansive S)
      (completionMapNonexpansive
        (completionFlattenNonexpansive S))).toFun := by
  constructor
  · exact completionFlatten_secondEmbed S
  · constructor
    · exact completionFlatten_map_unit S
    · exact completionFlatten_associative S

end Filtered

namespace External

variable {Sigma : Signature.{u}}
end External

namespace Free

variable {Sigma : Signature.{u}}

/-- Canonical generated Answer carried by an old value. -/
def generatedOld
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) : GeneratedAns D :=
  ⟨RawAns.old a, ⟨Expr.val a, rfl⟩⟩

@[simp] theorem generatedOld_val
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) :
    (generatedOld D a).1 = RawAns.old a := by
  rfl

/-- Apply one Resolution operation to two generated Answers. The underlying
    raw Answer is exactly `liftOp`; generation follows by choosing expression
    witnesses for the two inputs and adjoining one application node. -/
noncomputable def generatedOp
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : GeneratedAns D) : GeneratedAns D := by
  let ex : Expr Sigma D.Carrier := Classical.choose x.property
  let ey : Expr Sigma D.Carrier := Classical.choose y.property
  have hex : Expr.res D ex = x.1 := Classical.choose_spec x.property
  have hey : Expr.res D ey = y.1 := Classical.choose_spec y.property
  refine ⟨D.liftOp f x.1 y.1, ?_⟩
  refine ⟨Expr.app f ex ey, ?_⟩
  simp only [Expr.res]
  rw [hex, hey]

@[simp] theorem generatedOp_val
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : GeneratedAns D) :
    (generatedOp D f x y).1 = D.liftOp f x.1 y.1 := by
  rfl

/-- Old values remain injective inside generated Answers. -/
theorem generatedOld_injective
    (D : PartialAlg.{u,v} Sigma) :
    Function.Injective (generatedOld D) := by
  intro a b hab
  have hval : RawAns.old a = RawAns.old b :=
    congrArg Subtype.val hab
  cases hval
  rfl

namespace TotalAlg

/-- Folding a normalized/suspended Resolution application into any compatible
    total algebra is exactly the target algebra operation on the two folds. -/
theorem foldRaw_liftOp
    (D : PartialAlg.{u,v} Sigma)
    (T : TotalAlg D)
    (f : Sigma.Op)
    (x y : RawAns Sigma D.Carrier) :
    foldRaw D T (D.liftOp f x y) =
      T.op f (foldRaw D T x) (foldRaw D T y) := by
  cases x with
  | old a =>
      cases y with
      | old b =>
          cases hEval : D.eval f a b with
          | none =>
              simp [PartialAlg.liftOp, hEval, foldRaw]
          | some c =>
              simp only [PartialAlg.liftOp, hEval, foldRaw]
              exact (T.preserve f a b c hEval).symm
      | susp g l r =>
          rfl
  | susp g l r =>
      cases y <;> rfl

/-- Interpretation commutes with the generated Resolution operation. -/
theorem interp_generatedOp
    (D : PartialAlg.{u,v} Sigma)
    (T : TotalAlg D)
    (f : Sigma.Op)
    (x y : GeneratedAns D) :
    interp D T (generatedOp D f x y) =
      T.op f (interp D T x) (interp D T y) := by
  unfold interp
  rw [generatedOp_val]
  exact foldRaw_liftOp D T f x.1 y.1

end TotalAlg

/-- Already-defined old operations normalize inside the generated algebra. -/
theorem generatedOp_old_of_defined
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (a b c : D.Carrier)
    (h : D.eval f a b = some c) :
    generatedOp D f (generatedOld D a) (generatedOld D b) =
      generatedOld D c := by
  apply Subtype.ext
  change D.liftOp f (RawAns.old a) (RawAns.old b) = RawAns.old c
  simp [PartialAlg.liftOp, h]

end Free

namespace Filtered

/-- A jointly nonexpansive binary map preserves one finite stage in both
    arguments simultaneously. -/
structure BinaryNonexpansive
    (S : Space.{u}) (T : Space.{v}) (U : Space.{w}) where
  toFun : S.Carrier → T.Carrier → U.Carrier
  map_eqAt : ∀ n : Nat,
    ∀ {x x' : S.Carrier} {y y' : T.Carrier},
      S.eqAt n x x' → T.eqAt n y y' →
        U.eqAt n (toFun x y) (toFun x' y')

namespace BinaryNonexpansive

/-- Fixing the first argument of a jointly nonexpansive map leaves a
    nonexpansive unary map. -/
def leftSection
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (x : S.Carrier) : Nonexpansive T U where
  toFun := f.toFun x
  map_eqAt := by
    intro n y y' hyy
    exact f.map_eqAt n (S.eqAt_refl n x) hyy

/-- Fixing the second argument also leaves a nonexpansive unary map. -/
def rightSection
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (y : T.Carrier) : Nonexpansive S U where
  toFun := fun x => f.toFun x y
  map_eqAt := by
    intro n x x' hxx
    exact f.map_eqAt n hxx (T.eqAt_refl n y)

/-- Pointwise application to two Cauchy sequences is Cauchy. -/
theorem map_cauchy
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    {s : Nat → S.Carrier} {t : Nat → T.Carrier}
    (hs : Cauchy S s) (ht : Cauchy T t) :
    Cauchy U (fun k => f.toFun (s k) (t k)) := by
  intro n
  rcases hs n with ⟨Ns, hsN⟩
  rcases ht n with ⟨Nt, htN⟩
  refine ⟨Nat.max Ns Nt, ?_⟩
  intro i j hi hj
  exact f.map_eqAt n
    (hsN i j
      (Nat.le_trans (Nat.le_max_left Ns Nt) hi)
      (Nat.le_trans (Nat.le_max_left Ns Nt) hj))
    (htN i j
      (Nat.le_trans (Nat.le_max_right Ns Nt) hi)
      (Nat.le_trans (Nat.le_max_right Ns Nt) hj))

/-- Pointwise application preserves eventual equivalence at a fixed stage. -/
theorem map_sequenceEqAt
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (n : Nat)
    {s s' : Nat → S.Carrier}
    {t t' : Nat → T.Carrier}
    (hs : SequenceEqAt S n s s')
    (ht : SequenceEqAt T n t t') :
    SequenceEqAt U n
      (fun k => f.toFun (s k) (t k))
      (fun k => f.toFun (s' k) (t' k)) := by
  rcases hs with ⟨Ns, hsN⟩
  rcases ht with ⟨Nt, htN⟩
  refine ⟨Nat.max Ns Nt, ?_⟩
  intro k hk
  exact f.map_eqAt n
    (hsN k (Nat.le_trans (Nat.le_max_left Ns Nt) hk))
    (htN k (Nat.le_trans (Nat.le_max_right Ns Nt) hk))

/-- Pointwise application preserves full asymptotic sequence equivalence. -/
theorem map_sequenceEq
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    {s s' : Nat → S.Carrier}
    {t t' : Nat → T.Carrier}
    (hs : SequenceEq S s s')
    (ht : SequenceEq T t t') :
    SequenceEq U
      (fun k => f.toFun (s k) (t k))
      (fun k => f.toFun (s' k) (t' k)) := by
  intro n
  exact f.map_sequenceEqAt n (hs n) (ht n)

end BinaryNonexpansive

/-- Pointwise image of two packaged Cauchy representatives. -/
def mapBinaryCauchySeq
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (s : CauchySeq S) (t : CauchySeq T) : CauchySeq U where
  term := fun k => f.toFun (s.term k) (t.term k)
  cauchy := f.map_cauchy s.cauchy t.cauchy

/-- Every jointly nonexpansive binary map lifts pointwise to the Cauchy
    completions. -/
def completionBinaryMap
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (q : Completion S) (r : Completion T) : Completion U :=
  Quotient.liftOn₂ q r
    (fun s t => classOf U (mapBinaryCauchySeq f s t))
    (by
      intro s t s' t' hs ht
      apply Quotient.sound
      change SequenceEq S s.term s'.term at hs
      change SequenceEq T t.term t'.term at ht
      exact f.map_sequenceEq hs ht)

/-- The lifted binary operation extends the original map on embedded points. -/
theorem completionBinaryMap_embed
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (x : S.Carrier) (y : T.Carrier) :
    completionBinaryMap f (embed S x) (embed T y) =
      embed U (f.toFun x y) := by
  apply Quotient.sound
  exact sequenceEq_refl U (fun _ => f.toFun x y)

/-- The lifted binary map remains jointly nonexpansive on completions. -/
theorem completionBinaryMap_preserves_eqAt
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (n : Nat)
    {q q' : Completion S} {r r' : Completion T}
    (hq : CompletionEqAt S n q q')
    (hr : CompletionEqAt T n r r') :
    CompletionEqAt U n
      (completionBinaryMap f q r)
      (completionBinaryMap f q' r') := by
  revert hq hr
  refine Quotient.inductionOn q ?_
  intro s
  refine Quotient.inductionOn q' ?_
  intro s'
  refine Quotient.inductionOn r ?_
  intro t
  refine Quotient.inductionOn r' ?_
  intro t' hs ht
  change SequenceEqAt S n s.term s'.term at hs
  change SequenceEqAt T n t.term t'.term at ht
  change SequenceEqAt U n
    (fun k => f.toFun (s.term k) (t.term k))
    (fun k => f.toFun (s'.term k) (t'.term k))
  exact f.map_sequenceEqAt n hs ht

/-- Packaged jointly nonexpansive lift to completion spaces. -/
def completionBinaryNonexpansive
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U) :
    BinaryNonexpansive
      (completionSpace S) (completionSpace T) (completionSpace U) where
  toFun := completionBinaryMap f
  map_eqAt := by
    intro n q q' r r' hq hr
    exact completionBinaryMap_preserves_eqAt f n hq hr

/-- The pointwise completion lift is the unique jointly nonexpansive binary map
    between completions extending the original binary map. -/
theorem completionBinaryMap_unique
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (g : BinaryNonexpansive
      (completionSpace S) (completionSpace T) (completionSpace U))
    (hgEmbed : ∀ x : S.Carrier, ∀ y : T.Carrier,
      g.toFun (embed S x) (embed T y) = embed U (f.toFun x y)) :
    g.toFun = completionBinaryMap f := by
  let c : BinaryNonexpansive
      (completionSpace S) (completionSpace T) (completionSpace U) :=
    completionBinaryNonexpansive f
  have hLeft : ∀ x : S.Carrier,
      (g.leftSection (embed S x)).toFun =
        (c.leftSection (embed S x)).toFun := by
    intro x
    let fx : Nonexpansive T (completionSpace U) :=
      Nonexpansive.comp (completionUnit U) (f.leftSection x)
    have hgExt := completeExtension_unique fx
      (completionSpace_is_complete U)
      (g.leftSection (embed S x)) (by
        intro y
        exact hgEmbed x y)
    have hcExt := completeExtension_unique fx
      (completionSpace_is_complete U)
      (c.leftSection (embed S x)) (by
        intro y
        exact completionBinaryMap_embed f x y)
    exact hgExt.trans hcExt.symm
  funext q r
  let baseR : Nonexpansive S (completionSpace U) :=
    Nonexpansive.comp (c.rightSection r) (completionUnit S)
  have hgExt := completeExtension_unique baseR
    (completionSpace_is_complete U)
    (g.rightSection r) (by
      intro x
      exact congrFun (hLeft x) r)
  have hcExt := completeExtension_unique baseR
    (completionSpace_is_complete U)
    (c.rightSection r) (by
      intro x
      rfl)
  have hSections := hgExt.trans hcExt.symm
  exact congrFun hSections q

end Filtered

namespace External

variable {Sigma : Signature.{u}}

/-- Every Resolution operation is jointly nonexpansive for the finite-tag
    observational filtration. -/
noncomputable def generatedOperation
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) :
    Filtered.BinaryNonexpansive
      (generatedFilteredSpace D)
      (generatedFilteredSpace D)
      (generatedFilteredSpace D) where
  toFun := Free.generatedOp D f
  map_eqAt := by
    intro n x x' y y' hx hy
    change Free.GeneratedAns D at x x' y y'
    change ∀ T : FiniteTagAlg D n,
      Free.TotalAlg.interp D (T.toTotalAlg D)
          (Free.generatedOp D f x y) =
        Free.TotalAlg.interp D (T.toTotalAlg D)
          (Free.generatedOp D f x' y')
    change ∀ T : FiniteTagAlg D n,
      Free.TotalAlg.interp D (T.toTotalAlg D) x =
        Free.TotalAlg.interp D (T.toTotalAlg D) x' at hx
    change ∀ T : FiniteTagAlg D n,
      Free.TotalAlg.interp D (T.toTotalAlg D) y =
        Free.TotalAlg.interp D (T.toTotalAlg D) y' at hy
    intro T
    calc
      Free.TotalAlg.interp D (T.toTotalAlg D)
          (Free.generatedOp D f x y) =
        (T.toTotalAlg D).op f
          (Free.TotalAlg.interp D (T.toTotalAlg D) x)
          (Free.TotalAlg.interp D (T.toTotalAlg D) y) :=
        Free.TotalAlg.interp_generatedOp D (T.toTotalAlg D) f x y
      _ = (T.toTotalAlg D).op f
          (Free.TotalAlg.interp D (T.toTotalAlg D) x')
          (Free.TotalAlg.interp D (T.toTotalAlg D) y') :=
        Eq.trans
          (congrArg
            (fun z => (T.toTotalAlg D).op f z
              (Free.TotalAlg.interp D (T.toTotalAlg D) y))
            (hx T))
          (congrArg
            (fun z => (T.toTotalAlg D).op f
              (Free.TotalAlg.interp D (T.toTotalAlg D) x') z)
            (hy T))
      _ = Free.TotalAlg.interp D (T.toTotalAlg D)
          (Free.generatedOp D f x' y') :=
        (Free.TotalAlg.interp_generatedOp D
          (T.toTotalAlg D) f x' y').symm

/-- Canonical completed Resolution operation on the generic filtered
    completion of generated Answers. -/
noncomputable def completedGeneratedOp
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (q r : Filtered.Completion (generatedFilteredSpace D)) :
    Filtered.Completion (generatedFilteredSpace D) :=
  Filtered.completionBinaryMap (generatedOperation D f) q r

/-- The completed operation extends the generated Resolution operation. -/
theorem completedGeneratedOp_embed
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : Free.GeneratedAns D) :
    completedGeneratedOp D f
        (Filtered.embed (generatedFilteredSpace D) x)
        (Filtered.embed (generatedFilteredSpace D) y) =
      Filtered.embed (generatedFilteredSpace D)
        (Free.generatedOp D f x y) :=
  Filtered.completionBinaryMap_embed (generatedOperation D f) x y

/-- Completed Resolution operations preserve every completed finite stage. -/
theorem completedGeneratedOp_preserves_eqAt
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (n : Nat)
    {q q' r r' : Filtered.Completion (generatedFilteredSpace D)}
    (hq : Filtered.CompletionEqAt (generatedFilteredSpace D) n q q')
    (hr : Filtered.CompletionEqAt (generatedFilteredSpace D) n r r') :
    Filtered.CompletionEqAt (generatedFilteredSpace D) n
      (completedGeneratedOp D f q r)
      (completedGeneratedOp D f q' r') :=
  Filtered.completionBinaryMap_preserves_eqAt
    (generatedOperation D f) n hq hr

/-- The generic filtered completion carries a compatible conservative total
    algebra extending the original partial algebra. -/
noncomputable def completedResolutionTotalAlg
    (D : PartialAlg.{u,v} Sigma) : Free.TotalAlg D where
  Carrier := Filtered.Completion (generatedFilteredSpace D)
  embed := fun a =>
    Filtered.embed (generatedFilteredSpace D) (Free.generatedOld D a)
  embed_injective := by
    intro a b hab
    apply Free.generatedOld_injective D
    apply Filtered.embed_injective (generatedFilteredSpace D)
    exact hab
  op := completedGeneratedOp D
  preserve := by
    intro f a b c h
    calc
      completedGeneratedOp D f
          (Filtered.embed (generatedFilteredSpace D) (Free.generatedOld D a))
          (Filtered.embed (generatedFilteredSpace D) (Free.generatedOld D b)) =
        Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOp D f
            (Free.generatedOld D a) (Free.generatedOld D b)) :=
        completedGeneratedOp_embed D f
          (Free.generatedOld D a) (Free.generatedOld D b)
      _ = Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOld D c) :=
        congrArg (Filtered.embed (generatedFilteredSpace D))
          (Free.generatedOp_old_of_defined D f a b c h)

/-- Transport the completed operation to the previously defined specialized
    observational completion. -/
noncomputable def observationalCompletedOp
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (q r : ObservationalCompletion D) : ObservationalCompletion D :=
  filteredCompletionToObservational D
    (completedGeneratedOp D f
      (observationalCompletionToFiltered D q)
      (observationalCompletionToFiltered D r))

/-- The transported operation extends the generated operation under the
    specialized observational embedding. -/
theorem observationalCompletedOp_embed
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : Free.GeneratedAns D) :
    observationalCompletedOp D f
        (observationalCompletionEmbed D x)
        (observationalCompletionEmbed D y) =
      observationalCompletionEmbed D (Free.generatedOp D f x y) := by
  unfold observationalCompletedOp
  rw [observationalCompletionToFiltered_embed,
    observationalCompletionToFiltered_embed,
    completedGeneratedOp_embed,
    filteredCompletionToObservational_embed]

/-- The transported operation is jointly stage-compatible on the specialized
    observational completion. -/
theorem observationalCompletedOp_preserves_eqAt
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (n : Nat)
    {q q' r r' : ObservationalCompletion D}
    (hq : CompletionEqAt D n q q')
    (hr : CompletionEqAt D n r r') :
    CompletionEqAt D n
      (observationalCompletedOp D f q r)
      (observationalCompletedOp D f q' r') := by
  unfold observationalCompletedOp
  apply (filteredCompletionEqAt_iff_observationalCompletionEqAt
    D n _ _).1
  exact completedGeneratedOp_preserves_eqAt D f n
    ((observationalCompletionEqAt_iff_filteredCompletionEqAt
      D n q q').1 hq)
    ((observationalCompletionEqAt_iff_filteredCompletionEqAt
      D n r r').1 hr)

/-- The original observational completion therefore also carries the canonical
    compatible conservative total algebra. -/
noncomputable def observationalCompletedTotalAlg
    (D : PartialAlg.{u,v} Sigma) : Free.TotalAlg D where
  Carrier := ObservationalCompletion D
  embed := fun a =>
    observationalCompletionEmbed D (Free.generatedOld D a)
  embed_injective := by
    intro a b hab
    apply Free.generatedOld_injective D
    apply observationalCompletionEmbed_injective D
    exact hab
  op := observationalCompletedOp D
  preserve := by
    intro f a b c h
    calc
      observationalCompletedOp D f
          (observationalCompletionEmbed D (Free.generatedOld D a))
          (observationalCompletionEmbed D (Free.generatedOld D b)) =
        observationalCompletionEmbed D
          (Free.generatedOp D f
            (Free.generatedOld D a) (Free.generatedOld D b)) :=
        observationalCompletedOp_embed D f
          (Free.generatedOld D a) (Free.generatedOld D b)
      _ = observationalCompletionEmbed D (Free.generatedOld D c) :=
        congrArg (observationalCompletionEmbed D)
          (Free.generatedOp_old_of_defined D f a b c h)

end External

namespace External

variable {Sigma : Signature.{u}}
end External

namespace Filtered

/-- Extension of a jointly nonexpansive binary map into an arbitrary complete
    filtered target. It is obtained by first lifting into the target completion
    and then applying the inverse supplied by completeness. -/
noncomputable def completeBinaryExtension
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (hU : Complete U)
    (q : Completion S) (r : Completion T) : U.Carrier :=
  completionInverse U hU (completionBinaryMap f q r)

/-- The complete-target binary extension agrees with the original binary map
    on embedded source points. -/
theorem completeBinaryExtension_embed
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (hU : Complete U)
    (x : S.Carrier) (y : T.Carrier) :
    completeBinaryExtension f hU (embed S x) (embed T y) =
      f.toFun x y := by
  unfold completeBinaryExtension
  rw [completionBinaryMap_embed]
  exact embed_inverse_left U hU (f.toFun x y)

/-- The complete-target binary extension preserves each finite stage jointly
    in its two completion arguments. -/
theorem completeBinaryExtension_preserves_eqAt
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (hU : Complete U)
    (n : Nat)
    {q q' : Completion S} {r r' : Completion T}
    (hq : CompletionEqAt S n q q')
    (hr : CompletionEqAt T n r r') :
    U.eqAt n
      (completeBinaryExtension f hU q r)
      (completeBinaryExtension f hU q' r') := by
  apply (completionInverse_eqAt_iff U hU n
    (completionBinaryMap f q r)
    (completionBinaryMap f q' r')).1
  exact completionBinaryMap_preserves_eqAt f n hq hr

/-- Packaged jointly nonexpansive extension into a complete target. -/
noncomputable def completeBinaryExtensionNonexpansive
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (hU : Complete U) :
    BinaryNonexpansive (completionSpace S) (completionSpace T) U where
  toFun := completeBinaryExtension f hU
  map_eqAt := by
    intro n q q' r r' hq hr
    exact completeBinaryExtension_preserves_eqAt f hU n hq hr

/-- Binary reflector uniqueness: a jointly nonexpansive map out of two
    completions is determined by its values on pairs of embedded points. -/
theorem completeBinaryExtension_unique
    {S : Space.{u}} {T : Space.{v}} {U : Space.{w}}
    (f : BinaryNonexpansive S T U)
    (hU : Complete U)
    (g : BinaryNonexpansive
      (completionSpace S) (completionSpace T) U)
    (hgEmbed : ∀ x : S.Carrier, ∀ y : T.Carrier,
      g.toFun (embed S x) (embed T y) = f.toFun x y) :
    g.toFun = completeBinaryExtension f hU := by
  let c : BinaryNonexpansive
      (completionSpace S) (completionSpace T) U :=
    completeBinaryExtensionNonexpansive f hU
  have hLeft : ∀ x : S.Carrier,
      (g.leftSection (embed S x)).toFun =
        (c.leftSection (embed S x)).toFun := by
    intro x
    have hgExt := completeExtension_unique (f.leftSection x) hU
      (g.leftSection (embed S x)) (by
        intro y
        exact hgEmbed x y)
    have hcExt := completeExtension_unique (f.leftSection x) hU
      (c.leftSection (embed S x)) (by
        intro y
        exact completeBinaryExtension_embed f hU x y)
    exact hgExt.trans hcExt.symm
  funext q r
  let baseR : Nonexpansive S U :=
    Nonexpansive.comp (c.rightSection r) (completionUnit S)
  have hgExt := completeExtension_unique baseR hU
    (g.rightSection r) (by
      intro x
      exact congrFun (hLeft x) r)
  have hcExt := completeExtension_unique baseR hU
    (c.rightSection r) (by
      intro x
      rfl)
  have hSections := hgExt.trans hcExt.symm
  exact congrFun hSections q

end Filtered

namespace Free
namespace TotalAlg

variable {Sigma : Signature.{u}}

/-- Interpreting an old generated Answer is the old embedding. -/
@[simp] theorem interp_generatedOld
    (D : PartialAlg.{u,v} Sigma)
    (T : TotalAlg.{u,v,w} D)
    (a : D.Carrier) :
    interp D T (generatedOld D a) = T.embed a := by
  rfl

end TotalAlg
end Free

namespace External

variable {Sigma : Signature.{u}}

/-- A compatible total algebra equipped with a separated filtered structure.
    Its generated-Answer interpretation and every algebra operation are required
    to preserve finite observational stages. -/
structure FilteredTotalAlg
    (D : PartialAlg.{u,v} Sigma) where
  total : Free.TotalAlg.{u,v,w} D
  eqAt : Nat → total.Carrier → total.Carrier → Prop
  eqAt_refl : ∀ n : Nat, ∀ x : total.Carrier, eqAt n x x
  eqAt_symm : ∀ n : Nat, ∀ {x y : total.Carrier},
    eqAt n x y → eqAt n y x
  eqAt_trans : ∀ n : Nat, ∀ {x y z : total.Carrier},
    eqAt n x y → eqAt n y z → eqAt n x z
  eqAt_antitone : ∀ {n m : Nat}, n ≤ m →
    ∀ {x y : total.Carrier}, eqAt m x y → eqAt n x y
  separated : ∀ {x y : total.Carrier},
    (∀ n : Nat, eqAt n x y) → x = y
  interp_map_eqAt : ∀ n : Nat,
    ∀ {x y : Free.GeneratedAns D},
      FiniteObservationBall D n x y →
        eqAt n
          (Free.TotalAlg.interp D total x)
          (Free.TotalAlg.interp D total y)
  op_map_eqAt : ∀ f : Sigma.Op, ∀ n : Nat,
    ∀ {a a' b b' : total.Carrier},
      eqAt n a a' → eqAt n b b' →
        eqAt n (total.op f a b) (total.op f a' b')

namespace FilteredTotalAlg

/-- The filtered space underlying a filtered compatible total algebra. -/
def toSpace
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D) : Filtered.Space.{w} where
  Carrier := T.total.Carrier
  eqAt := T.eqAt
  eqAt_refl := T.eqAt_refl
  eqAt_symm := T.eqAt_symm
  eqAt_trans := T.eqAt_trans
  eqAt_antitone := T.eqAt_antitone
  separated := T.separated

/-- Interpretation of generated Answers as a nonexpansive map. -/
def interpNonexpansive
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D) :
    Filtered.Nonexpansive (generatedFilteredSpace D) T.toSpace where
  toFun := Free.TotalAlg.interp D T.total
  map_eqAt := by
    intro n x y hxy
    change Free.GeneratedAns D at x y
    exact T.interp_map_eqAt n hxy

/-- Each target operation as a jointly nonexpansive binary map. -/
def operationNonexpansive
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (f : Sigma.Op) :
    Filtered.BinaryNonexpansive T.toSpace T.toSpace T.toSpace where
  toFun := T.total.op f
  map_eqAt := by
    intro n a a' b b' ha hb
    exact T.op_map_eqAt f n ha hb

/-- The binary target operation after interpreting two generated Answers. -/
def interpretedGeneratedOperation
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (f : Sigma.Op) :
    Filtered.BinaryNonexpansive
      (generatedFilteredSpace D)
      (generatedFilteredSpace D)
      T.toSpace where
  toFun := fun x y =>
    T.total.op f
      (Free.TotalAlg.interp D T.total x)
      (Free.TotalAlg.interp D T.total y)
  map_eqAt := by
    intro n x x' y y' hx hy
    change Free.GeneratedAns D at x x' y y'
    exact T.op_map_eqAt f n
      (T.interp_map_eqAt n hx)
      (T.interp_map_eqAt n hy)

/-- Canonical interpretation of the completed Resolution carrier in a complete
    filtered compatible target. -/
noncomputable def completedInterp
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (q : Filtered.Completion (generatedFilteredSpace D)) :
    T.total.Carrier :=
  Filtered.completeExtension T.interpNonexpansive hT q

/-- The completed interpretation is nonexpansive. -/
noncomputable def completedInterpNonexpansive
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace) :
    Filtered.Nonexpansive
      (Filtered.completionSpace (generatedFilteredSpace D))
      T.toSpace :=
  Filtered.completeExtensionNonexpansive T.interpNonexpansive hT

/-- The completed interpretation extends ordinary generated interpretation. -/
theorem completedInterp_embed
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (x : Free.GeneratedAns D) :
    T.completedInterp hT
        (Filtered.embed (generatedFilteredSpace D) x) =
      Free.TotalAlg.interp D T.total x :=
  Filtered.completeExtension_embed T.interpNonexpansive hT x

/-- First canonical binary extension candidate: apply the completed Resolution
    operation and then interpret. -/
noncomputable def completedInterpAfterGeneratedOp
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (f : Sigma.Op) :
    Filtered.BinaryNonexpansive
      (Filtered.completionSpace (generatedFilteredSpace D))
      (Filtered.completionSpace (generatedFilteredSpace D))
      T.toSpace where
  toFun := fun q r =>
    T.completedInterp hT (completedGeneratedOp D f q r)
  map_eqAt := by
    intro n q q' r r' hq hr
    exact (T.completedInterpNonexpansive hT).map_eqAt n
      (completedGeneratedOp_preserves_eqAt D f n hq hr)

/-- Second canonical binary extension candidate: interpret both arguments and
    then apply the target operation. -/
noncomputable def targetOpAfterCompletedInterp
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (f : Sigma.Op) :
    Filtered.BinaryNonexpansive
      (Filtered.completionSpace (generatedFilteredSpace D))
      (Filtered.completionSpace (generatedFilteredSpace D))
      T.toSpace where
  toFun := fun q r =>
    T.total.op f (T.completedInterp hT q) (T.completedInterp hT r)
  map_eqAt := by
    intro n q q' r r' hq hr
    exact T.op_map_eqAt f n
      ((T.completedInterpNonexpansive hT).map_eqAt n hq)
      ((T.completedInterpNonexpansive hT).map_eqAt n hr)

/-- The first candidate extends the interpreted generated operation. -/
theorem completedInterpAfterGeneratedOp_embed
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (f : Sigma.Op)
    (x y : Free.GeneratedAns D) :
    (T.completedInterpAfterGeneratedOp hT f).toFun
        (Filtered.embed (generatedFilteredSpace D) x)
        (Filtered.embed (generatedFilteredSpace D) y) =
      (T.interpretedGeneratedOperation f).toFun x y := by
  change T.completedInterp hT
      (completedGeneratedOp D f
        (Filtered.embed (generatedFilteredSpace D) x)
        (Filtered.embed (generatedFilteredSpace D) y)) =
    T.total.op f
      (Free.TotalAlg.interp D T.total x)
      (Free.TotalAlg.interp D T.total y)
  rw [completedGeneratedOp_embed, T.completedInterp_embed]
  exact Free.TotalAlg.interp_generatedOp D T.total f x y

/-- The second candidate extends the same interpreted generated operation. -/
theorem targetOpAfterCompletedInterp_embed
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (f : Sigma.Op)
    (x y : Free.GeneratedAns D) :
    (T.targetOpAfterCompletedInterp hT f).toFun
        (Filtered.embed (generatedFilteredSpace D) x)
        (Filtered.embed (generatedFilteredSpace D) y) =
      (T.interpretedGeneratedOperation f).toFun x y := by
  change T.total.op f
      (T.completedInterp hT
        (Filtered.embed (generatedFilteredSpace D) x))
      (T.completedInterp hT
        (Filtered.embed (generatedFilteredSpace D) y)) =
    T.total.op f
      (Free.TotalAlg.interp D T.total x)
      (Free.TotalAlg.interp D T.total y)
  rw [T.completedInterp_embed, T.completedInterp_embed]

/-- The canonical completed interpretation is an algebra homomorphism. -/
theorem completedInterp_map_op
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (f : Sigma.Op)
    (q r : Filtered.Completion (generatedFilteredSpace D)) :
    T.completedInterp hT (completedGeneratedOp D f q r) =
      T.total.op f
        (T.completedInterp hT q)
        (T.completedInterp hT r) := by
  let base := T.interpretedGeneratedOperation f
  let left := T.completedInterpAfterGeneratedOp hT f
  let right := T.targetOpAfterCompletedInterp hT f
  have hLeft := Filtered.completeBinaryExtension_unique base hT left (by
    intro x y
    exact T.completedInterpAfterGeneratedOp_embed hT f x y)
  have hRight := Filtered.completeBinaryExtension_unique base hT right (by
    intro x y
    exact T.targetOpAfterCompletedInterp_embed hT f x y)
  have hEq : left.toFun = right.toFun := hLeft.trans hRight.symm
  have hAt := congrFun (congrFun hEq q) r
  change
    @Eq T.toSpace.Carrier
      (T.completedInterp hT (completedGeneratedOp D f q r))
      (T.total.op f
        (T.completedInterp hT q)
        (T.completedInterp hT r))
  simpa [left, right, completedInterpAfterGeneratedOp,
    targetOpAfterCompletedInterp] using hAt

/-- The canonical completed interpretation also preserves old embedded values. -/
theorem completedInterp_map_old
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (a : D.Carrier) :
    T.completedInterp hT
        (Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOld D a)) =
      T.total.embed a := by
  rw [T.completedInterp_embed]
  exact Free.TotalAlg.interp_generatedOld D T.total a

/-- Reflector uniqueness for the completed interpretation. -/
theorem completedInterp_unique
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (g : Filtered.Nonexpansive
      (Filtered.completionSpace (generatedFilteredSpace D))
      T.toSpace)
    (hg : ∀ x : Free.GeneratedAns D,
      g.toFun (Filtered.embed (generatedFilteredSpace D) x) =
        Free.TotalAlg.interp D T.total x) :
    g.toFun = T.completedInterp hT :=
  Filtered.completeExtension_unique T.interpNonexpansive hT g hg

/-- Universal property of the completed Resolution algebra: its canonical map
    into every complete filtered compatible total algebra preserves old values
    and operations, extends generated interpretation, and is the unique
    nonexpansive extension of that interpretation. -/
theorem completedResolutionAlgebra_universal
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace) :
    (∀ x : Free.GeneratedAns D,
      T.completedInterp hT
          (Filtered.embed (generatedFilteredSpace D) x) =
        Free.TotalAlg.interp D T.total x) ∧
    (∀ a : D.Carrier,
      T.completedInterp hT
          (Filtered.embed (generatedFilteredSpace D)
            (Free.generatedOld D a)) =
        T.total.embed a) ∧
    (∀ f : Sigma.Op,
      ∀ q r : Filtered.Completion (generatedFilteredSpace D),
        T.completedInterp hT (completedGeneratedOp D f q r) =
          T.total.op f
            (T.completedInterp hT q)
            (T.completedInterp hT r)) ∧
    (∀ g : Filtered.Nonexpansive
        (Filtered.completionSpace (generatedFilteredSpace D))
        T.toSpace,
      (∀ x : Free.GeneratedAns D,
        g.toFun (Filtered.embed (generatedFilteredSpace D) x) =
          Free.TotalAlg.interp D T.total x) →
        g.toFun = T.completedInterp hT) := by
  constructor
  · exact T.completedInterp_embed hT
  · constructor
    · exact T.completedInterp_map_old hT
    · constructor
      · exact T.completedInterp_map_op hT
      · intro g hg
        exact T.completedInterp_unique hT g hg

end FilteredTotalAlg

end External

namespace External

variable {Sigma : Signature.{u}}
end External

universe z

namespace Free

variable {Sigma : Signature.{u}}

/-- Generated Answer obtained directly from one source expression. -/
def generatedOfExpr
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) : GeneratedAns D :=
  ⟨Expr.res D e, ⟨e, rfl⟩⟩

@[simp] theorem generatedOfExpr_val
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) :
    generatedOfExpr D (Expr.val a) = generatedOld D a := by
  apply Subtype.ext
  rfl

@[simp] theorem generatedOfExpr_app
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : Expr Sigma D.Carrier) :
    generatedOfExpr D (Expr.app f x y) =
      generatedOp D f (generatedOfExpr D x) (generatedOfExpr D y) := by
  apply Subtype.ext
  rfl

end Free

namespace External

variable {Sigma : Signature.{u}}

/-- Interpretation in the canonical completed total algebra sends an expression
    exactly to the embedded generated Answer represented by that expression. -/
theorem completedResolution_interp_generatedOfExpr
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    Free.TotalAlg.interp D (completedResolutionTotalAlg D)
        (Free.generatedOfExpr D e) =
      Filtered.embed (generatedFilteredSpace D)
        (Free.generatedOfExpr D e) := by
  induction e with
  | val a =>
      rw [Free.generatedOfExpr_val]
      change Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOld D a) =
        Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOld D a)
      rfl
  | app f x y ihx ihy =>
      rw [Free.generatedOfExpr_app]
      rw [Free.TotalAlg.interp_generatedOp]
      change completedGeneratedOp D f
          (Free.TotalAlg.interp D (completedResolutionTotalAlg D)
            (Free.generatedOfExpr D x))
          (Free.TotalAlg.interp D (completedResolutionTotalAlg D)
            (Free.generatedOfExpr D y)) =
        Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOp D f
            (Free.generatedOfExpr D x)
            (Free.generatedOfExpr D y))
      rw [ihx, ihy]
      exact completedGeneratedOp_embed D f
        (Free.generatedOfExpr D x) (Free.generatedOfExpr D y)

/-- Every generated Answer is interpreted by the completed total algebra as its
    own canonical embedded completion point. -/
theorem completedResolution_interp
    (D : PartialAlg.{u,v} Sigma)
    (x : Free.GeneratedAns D) :
    Free.TotalAlg.interp D (completedResolutionTotalAlg D) x =
      Filtered.embed (generatedFilteredSpace D) x := by
  rcases x.property with ⟨e, he⟩
  have hx : x = Free.generatedOfExpr D e := by
    apply Subtype.ext
    exact he.symm
  rw [hx]
  exact completedResolution_interp_generatedOfExpr D e

/-- The canonical completed total algebra, now equipped with its completed
    finite-stage filtration. -/
noncomputable def completedResolutionFilteredTotalAlg
    (D : PartialAlg.{u,v} Sigma) : FilteredTotalAlg D where
  total := completedResolutionTotalAlg D
  eqAt := Filtered.CompletionEqAt (generatedFilteredSpace D)
  eqAt_refl := Filtered.completionEqAt_refl (generatedFilteredSpace D)
  eqAt_symm := Filtered.completionEqAt_symm (generatedFilteredSpace D)
  eqAt_trans := Filtered.completionEqAt_trans (generatedFilteredSpace D)
  eqAt_antitone := by
    intro n m hnm q r hqr
    exact Filtered.completionEqAt_antitone
      (generatedFilteredSpace D) hnm hqr
  separated := by
    intro q r hall
    exact (Filtered.forall_completionEqAt_iff_eq
      (generatedFilteredSpace D) q r).1 hall
  interp_map_eqAt := by
    intro n x y hxy
    rw [completedResolution_interp D x,
      completedResolution_interp D y]
    exact (Filtered.completionEqAt_embed_iff
      (generatedFilteredSpace D) n x y).2 hxy
  op_map_eqAt := by
    intro f n q q' r r' hq hr
    exact completedGeneratedOp_preserves_eqAt D f n hq hr

/-- The packaged completed Resolution algebra is complete. -/
theorem completedResolutionFilteredTotalAlg_complete
    (D : PartialAlg.{u,v} Sigma) :
    Filtered.Complete (completedResolutionFilteredTotalAlg D).toSpace := by
  change Filtered.Complete
    (Filtered.completionSpace (generatedFilteredSpace D))
  exact Filtered.completionSpace_is_complete (generatedFilteredSpace D)

namespace FilteredTotalAlg

/-- Nonexpansive algebra homomorphisms preserving the old embedding and all
    operations. -/
structure Hom
    {D : PartialAlg.{u,v} Sigma}
    (A : FilteredTotalAlg.{u,v,w} D)
    (B : FilteredTotalAlg.{u,v,z} D) where
  toFun : A.total.Carrier → B.total.Carrier
  map_eqAt : ∀ n : Nat, ∀ {x y : A.total.Carrier},
    A.eqAt n x y → B.eqAt n (toFun x) (toFun y)
  map_embed : ∀ a : D.Carrier,
    toFun (A.total.embed a) = B.total.embed a
  map_op : ∀ f : Sigma.Op, ∀ x y : A.total.Carrier,
    toFun (A.total.op f x y) =
      B.total.op f (toFun x) (toFun y)

namespace Hom

/-- Underlying nonexpansive map of a filtered algebra homomorphism. -/
def toNonexpansive
    {D : PartialAlg.{u,v} Sigma}
    {A : FilteredTotalAlg.{u,v,w} D}
    {B : FilteredTotalAlg.{u,v,z} D}
    (F : Hom A B) : Filtered.Nonexpansive A.toSpace B.toSpace where
  toFun := F.toFun
  map_eqAt := F.map_eqAt

/-- Identity filtered algebra homomorphism. -/
def id
    {D : PartialAlg.{u,v} Sigma}
    (A : FilteredTotalAlg.{u,v,w} D) : Hom A A where
  toFun := fun x => x
  map_eqAt := by
    intro n x y hxy
    exact hxy
  map_embed := by
    intro a
    rfl
  map_op := by
    intro f x y
    rfl

/-- A filtered algebra homomorphism commutes with folding raw Answers. -/
theorem map_foldRaw
    {D : PartialAlg.{u,v} Sigma}
    {A : FilteredTotalAlg.{u,v,w} D}
    {B : FilteredTotalAlg.{u,v,z} D}
    (F : Hom A B)
    (t : RawAns Sigma D.Carrier) :
    F.toFun (Free.TotalAlg.foldRaw D A.total t) =
      Free.TotalAlg.foldRaw D B.total t := by
  induction t with
  | old a =>
      exact F.map_embed a
  | susp f x y ihx ihy =>
      simp only [Free.TotalAlg.foldRaw]
      rw [F.map_op, ihx, ihy]

/-- Consequently, filtered algebra homomorphisms commute with generated-Answer
    interpretation. -/
theorem map_interp
    {D : PartialAlg.{u,v} Sigma}
    {A : FilteredTotalAlg.{u,v,w} D}
    {B : FilteredTotalAlg.{u,v,z} D}
    (F : Hom A B)
    (x : Free.GeneratedAns D) :
    F.toFun (Free.TotalAlg.interp D A.total x) =
      Free.TotalAlg.interp D B.total x := by
  unfold Free.TotalAlg.interp
  exact F.map_foldRaw x.1

end Hom

/-- Canonical filtered algebra homomorphism from the completed Resolution
    algebra into any complete filtered compatible total algebra. -/
noncomputable def completedResolutionHom
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace) :
    Hom (completedResolutionFilteredTotalAlg D) T where
  toFun := T.completedInterp hT
  map_eqAt := by
    intro n q r hqr
    exact (T.completedInterpNonexpansive hT).map_eqAt n hqr
  map_embed := by
    intro a
    change T.completedInterp hT
        (Filtered.embed (generatedFilteredSpace D)
          (Free.generatedOld D a)) =
      T.total.embed a
    exact T.completedInterp_map_old hT a
  map_op := by
    intro f q r
    change T.completedInterp hT (completedGeneratedOp D f q r) =
      T.total.op f
        (T.completedInterp hT q)
        (T.completedInterp hT r)
    exact T.completedInterp_map_op hT f q r

/-- Any filtered algebra homomorphism out of the completed Resolution algebra
    agrees with generated interpretation on the dense embedded subalgebra. -/
theorem hom_from_completed_agrees_on_generated
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (F : Hom (completedResolutionFilteredTotalAlg D) T)
    (x : Free.GeneratedAns D) :
    F.toFun (Filtered.embed (generatedFilteredSpace D) x) =
      Free.TotalAlg.interp D T.total x := by
  calc
    F.toFun (Filtered.embed (generatedFilteredSpace D) x) =
        F.toFun
          (Free.TotalAlg.interp D
            (completedResolutionFilteredTotalAlg D).total x) :=
      congrArg F.toFun (completedResolution_interp D x).symm
    _ = Free.TotalAlg.interp D T.total x := F.map_interp x

/-- Initiality: into every complete filtered compatible total algebra there is
    exactly one underlying nonexpansive algebra-homomorphism function from the
    completed Resolution algebra. -/
theorem completedResolutionHom_unique
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace)
    (F : Hom (completedResolutionFilteredTotalAlg D) T) :
    F.toFun = (completedResolutionHom T hT).toFun := by
  have hUnique := T.completedInterp_unique hT F.toNonexpansive (by
    intro x
    exact hom_from_completed_agrees_on_generated T F x)
  exact hUnique

/-- The universal initial-complete-algebra package. -/
theorem completedResolutionFilteredAlgebra_initial
    {D : PartialAlg.{u,v} Sigma}
    (T : FilteredTotalAlg.{u,v,w} D)
    (hT : Filtered.Complete T.toSpace) :
    Filtered.Complete (completedResolutionFilteredTotalAlg D).toSpace ∧
    (∀ F : Hom (completedResolutionFilteredTotalAlg D) T,
      F.toFun = (completedResolutionHom T hT).toFun) := by
  constructor
  · exact completedResolutionFilteredTotalAlg_complete D
  · intro F
    exact completedResolutionHom_unique T hT F

/-- The canonical map from the completed Resolution algebra to itself is the
    identity function. -/
theorem completedResolutionHom_self
    (D : PartialAlg.{u,v} Sigma) :
    (completedResolutionHom
      (completedResolutionFilteredTotalAlg D)
      (completedResolutionFilteredTotalAlg_complete D)).toFun =
        fun q => q := by
  have h := completedResolutionHom_unique
    (completedResolutionFilteredTotalAlg D)
    (completedResolutionFilteredTotalAlg_complete D)
    (Hom.id (completedResolutionFilteredTotalAlg D))
  exact h.symm

end FilteredTotalAlg

end External

namespace External

variable {Sigma : Signature.{u}}
end External

universe q

/-- Binary algebraic terms over the Resolution signature and an arbitrary
    variable type. -/
inductive AlgebraTerm
    (Sigma : Signature.{u}) (V : Type q) where
  | var : V -> AlgebraTerm Sigma V
  | app : Sigma.Op -> AlgebraTerm Sigma V -> AlgebraTerm Sigma V ->
      AlgebraTerm Sigma V

namespace AlgebraTerm

variable {Sigma : Signature.{u}}
variable {V : Type q}

/-- Evaluate an algebraic term in the generated Resolution algebra. -/
noncomputable def evalGenerated
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D) :
    AlgebraTerm Sigma V -> Free.GeneratedAns D
  | .var x => rho x
  | .app f s t =>
      Free.generatedOp D f
        (evalGenerated D rho s)
        (evalGenerated D rho t)

@[simp] theorem evalGenerated_var
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (x : V) :
    evalGenerated D rho (.var x) = rho x := by
  rfl

@[simp] theorem evalGenerated_app
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (f : Sigma.Op)
    (s t : AlgebraTerm Sigma V) :
    evalGenerated D rho (.app f s t) =
      Free.generatedOp D f
        (evalGenerated D rho s)
        (evalGenerated D rho t) := by
  rfl

end AlgebraTerm

namespace External

variable {Sigma : Signature.{u}}
variable {V : Type q}

/-- Evaluate an algebraic term in the canonical completed Resolution algebra. -/
noncomputable def AlgebraTerm.evalCompleted
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D)) :
    AlgebraTerm Sigma V ->
      Filtered.Completion (generatedFilteredSpace D)
  | .var x => rho x
  | .app f s t =>
      completedGeneratedOp D f
        (AlgebraTerm.evalCompleted D rho s)
        (AlgebraTerm.evalCompleted D rho t)

@[simp] theorem AlgebraTerm.evalCompleted_var
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (x : V) :
    AlgebraTerm.evalCompleted D rho (.var x) = rho x := by
  rfl

@[simp] theorem AlgebraTerm.evalCompleted_app
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (f : Sigma.Op)
    (s t : AlgebraTerm Sigma V) :
    AlgebraTerm.evalCompleted D rho (.app f s t) =
      completedGeneratedOp D f
        (AlgebraTerm.evalCompleted D rho s)
        (AlgebraTerm.evalCompleted D rho t) := by
  rfl

/-- Evaluation of a term on embedded generated values is exactly the embedding
    of its generated evaluation. -/
theorem AlgebraTerm.evalCompleted_embed
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (t : AlgebraTerm Sigma V) :
    AlgebraTerm.evalCompleted D
        (fun x => Filtered.embed (generatedFilteredSpace D) (rho x)) t =
      Filtered.embed (generatedFilteredSpace D)
        (AlgebraTerm.evalGenerated D rho t) := by
  induction t with
  | var x =>
      rfl
  | app f s t ihs iht =>
      simp only [AlgebraTerm.evalCompleted_app,
        AlgebraTerm.evalGenerated_app]
      rw [ihs, iht]
      exact completedGeneratedOp_embed D f
        (AlgebraTerm.evalGenerated D rho s)
        (AlgebraTerm.evalGenerated D rho t)

/-- Term evaluation is jointly finite-stage compatible in all variables. -/
theorem AlgebraTerm.evalCompleted_map_eqAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (rho sigma : V -> Filtered.Completion (generatedFilteredSpace D))
    (t : AlgebraTerm Sigma V)
    (hvars : forall x : V,
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (rho x) (sigma x)) :
    Filtered.CompletionEqAt (generatedFilteredSpace D) n
      (AlgebraTerm.evalCompleted D rho t)
      (AlgebraTerm.evalCompleted D sigma t) := by
  induction t with
  | var x =>
      exact hvars x
  | app f s t ihs iht =>
      simp only [AlgebraTerm.evalCompleted_app]
      exact completedGeneratedOp_preserves_eqAt D f n ihs iht

/-- At a fixed finite stage, choose one generated approximation for every
    completed variable assignment. -/
noncomputable def completionAssignmentApprox
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D)) :
    V -> Free.GeneratedAns D :=
  fun x => Classical.choose
    (Filtered.embed_stage_dense
      (generatedFilteredSpace D) n (rho x))

/-- The chosen assignment approximates the completed assignment at the selected
    finite stage. -/
theorem completionAssignmentApprox_spec
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (x : V) :
    Filtered.CompletionEqAt (generatedFilteredSpace D) n
      (rho x)
      (Filtered.embed (generatedFilteredSpace D)
        (completionAssignmentApprox D n rho x)) :=
  Classical.choose_spec
    (Filtered.embed_stage_dense
      (generatedFilteredSpace D) n (rho x))

/-- Equational transfer from the dense generated Resolution algebra to its
    completion. Any term equation valid for every generated assignment is
    valid for every completed assignment. -/
theorem generatedEquation_transfers_to_completion
    (D : PartialAlg.{u,v} Sigma)
    (lhs rhs : AlgebraTerm Sigma V)
    (hGenerated : forall rho : V -> Free.GeneratedAns D,
      AlgebraTerm.evalGenerated D rho lhs =
        AlgebraTerm.evalGenerated D rho rhs) :
    forall rho : V -> Filtered.Completion (generatedFilteredSpace D),
      AlgebraTerm.evalCompleted D rho lhs =
        AlgebraTerm.evalCompleted D rho rhs := by
  intro rho
  apply (Filtered.forall_completionEqAt_iff_eq
    (generatedFilteredSpace D)
    (AlgebraTerm.evalCompleted D rho lhs)
    (AlgebraTerm.evalCompleted D rho rhs)).1
  intro n
  let approx : V -> Free.GeneratedAns D :=
    completionAssignmentApprox D n rho
  have hLeft :
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (AlgebraTerm.evalCompleted D rho lhs)
        (AlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          lhs) :=
    AlgebraTerm.evalCompleted_map_eqAt D n rho
      (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
      lhs (by
        intro x
        exact completionAssignmentApprox_spec D n rho x)
  have hRight :
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (AlgebraTerm.evalCompleted D rho rhs)
        (AlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          rhs) :=
    AlgebraTerm.evalCompleted_map_eqAt D n rho
      (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
      rhs (by
        intro x
        exact completionAssignmentApprox_spec D n rho x)
  have hDense :
      AlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          lhs =
        AlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          rhs := by
    calc
      AlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          lhs =
        Filtered.embed (generatedFilteredSpace D)
          (AlgebraTerm.evalGenerated D approx lhs) :=
        AlgebraTerm.evalCompleted_embed D approx lhs
      _ = Filtered.embed (generatedFilteredSpace D)
          (AlgebraTerm.evalGenerated D approx rhs) :=
        congrArg (Filtered.embed (generatedFilteredSpace D))
          (hGenerated approx)
      _ = AlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          rhs :=
        (AlgebraTerm.evalCompleted_embed D approx rhs).symm
  rw [hDense] at hLeft
  exact Filtered.completionEqAt_trans (generatedFilteredSpace D) n
    hLeft
    (Filtered.completionEqAt_symm (generatedFilteredSpace D) n hRight)

/-- Exact equational conservativity: a term equation holds throughout the
    canonical completion if and only if it already holds in the generated
    Resolution algebra. -/
theorem completionEquation_iff_generatedEquation
    (D : PartialAlg.{u,v} Sigma)
    (lhs rhs : AlgebraTerm Sigma V) :
    (forall rho : V -> Filtered.Completion (generatedFilteredSpace D),
      AlgebraTerm.evalCompleted D rho lhs =
        AlgebraTerm.evalCompleted D rho rhs) <->
    (forall rho : V -> Free.GeneratedAns D,
      AlgebraTerm.evalGenerated D rho lhs =
        AlgebraTerm.evalGenerated D rho rhs) := by
  constructor
  · intro hCompletion rho
    apply Filtered.embed_injective (generatedFilteredSpace D)
    have h := hCompletion
      (fun x => Filtered.embed (generatedFilteredSpace D) (rho x))
    rw [AlgebraTerm.evalCompleted_embed D rho lhs,
      AlgebraTerm.evalCompleted_embed D rho rhs] at h
    exact h
  · intro hGenerated
    exact generatedEquation_transfers_to_completion D lhs rhs hGenerated

end External

namespace External

variable {Sigma : Signature.{u}}
end External

namespace External
namespace NatArithmetic

/-- A concrete arithmetic signature with total addition and multiplication and
    partial division. -/
inductive Op where
  | add
  | mul
  | div
  deriving DecidableEq, Repr

/-- Arithmetic signature used for the first concrete Resolution
    instantiation. This is transparent so `signature.Op` reduces to `Op`. -/
abbrev signature : Signature where
  Op := Op

/-- Natural-number arithmetic with division undefined exactly at denominator
    zero. -/
def eval (f : Op) (a b : Nat) : Option Nat :=
  match f with
  | .add => some (a + b)
  | .mul => some (a * b)
  | .div => if b = 0 then none else some (a / b)

/-- The concrete partial arithmetic algebra. This is an abbreviation so the
    old carrier remains transparently visible as `Nat` in concrete proofs. -/
abbrev alg : PartialAlg signature where
  Carrier := Nat
  eval := eval

@[simp] theorem eval_add (a b : Nat) :
    eval Op.add a b = some (a + b) := by
  rfl

@[simp] theorem eval_mul (a b : Nat) :
    eval Op.mul a b = some (a * b) := by
  rfl

@[simp] theorem eval_div_zero (a : Nat) :
    eval Op.div a 0 = none := by
  simp [eval]

@[simp] theorem eval_div_of_ne_zero
    (a b : Nat) (hb : b ≠ 0) :
    eval Op.div a b = some (a / b) := by
  simp [eval, hb]

/-- Generated Resolution Answers for the arithmetic algebra. -/
abbrev Answer := Free.GeneratedAns alg

/-- The generated Answer representing an old natural number. -/
def old (a : Nat) : Answer :=
  Free.generatedOld alg a

/-- Generated addition of two old natural numbers. -/
noncomputable def add (a b : Nat) : Answer :=
  Free.generatedOp alg Op.add (old a) (old b)

/-- Generated multiplication of two old natural numbers. -/
noncomputable def multiply (a b : Nat) : Answer :=
  Free.generatedOp alg Op.mul (old a) (old b)

/-- Generated division of two old natural numbers. When the denominator is
    zero, this is a structured suspended Answer rather than absence. -/
noncomputable def divide (a b : Nat) : Answer :=
  Free.generatedOp alg Op.div (old a) (old b)

@[simp] theorem old_val (a : Nat) :
    (old a).1 = RawAns.old a := by
  rfl

@[simp] theorem divide_val (a b : Nat) :
    (divide a b).1 =
      alg.liftOp Op.div (RawAns.old a) (RawAns.old b) := by
  rfl

/-- Addition remains ordinary addition on the old carrier. -/
theorem add_normalizes (a b : Nat) :
    add a b = old (a + b) := by
  simpa [add, old] using
    (Free.generatedOp_old_of_defined
      alg Op.add a b (a + b) (eval_add a b))

/-- Multiplication remains ordinary multiplication on the old carrier. -/
theorem multiply_normalizes (a b : Nat) :
    multiply a b = old (a * b) := by
  simpa [multiply, old] using
    (Free.generatedOp_old_of_defined
      alg Op.mul a b (a * b) (eval_mul a b))

/-- Division by a nonzero denominator remains ordinary natural-number
    division. -/
theorem divide_normalizes_of_ne_zero
    (a b : Nat) (hb : b ≠ 0) :
    divide a b = old (a / b) := by
  simpa [divide, old] using
    (Free.generatedOp_old_of_defined
      alg Op.div a b (a / b)
      (eval_div_of_ne_zero a b hb))

/-- Division by zero has an explicit suspended raw form. -/
@[simp] theorem divide_zero_raw (a : Nat) :
    (divide a 0).1 =
      RawAns.susp Op.div (RawAns.old a) (RawAns.old (0 : Nat)) := by
  rw [divide_val]
  rfl

/-- Read the old value stored in the left child of a suspended arithmetic
    Answer. The fallback branches are irrelevant to the injectivity proof. -/
def leftOldValue : RawAns signature Nat -> Nat
  | .old a => a
  | .susp _ (.old a) _ => a
  | .susp _ (.susp _ _ _) _ => 0

/-- Division-by-zero Answers retain the numerator rather than collapsing all
    singular divisions to one undifferentiated value. -/
theorem divide_zero_injective :
    Function.Injective (fun a : Nat => divide a 0) := by
  intro a b hab
  have hraw :
      RawAns.susp Op.div (RawAns.old a) (RawAns.old (0 : Nat)) =
        RawAns.susp Op.div (RawAns.old b) (RawAns.old (0 : Nat)) := by
    simpa only [divide_zero_raw] using congrArg Subtype.val hab
  have hnum := congrArg leftOldValue hraw
  simpa [leftOldValue] using hnum

/-- Distinguished concrete `0 / 0` Resolution Answer. -/
noncomputable def zeroDivZero : Answer :=
  divide 0 0

@[simp] theorem zeroDivZero_raw :
    zeroDivZero.1 =
      RawAns.susp Op.div
        (RawAns.old (0 : Nat)) (RawAns.old (0 : Nat)) := by
  simpa [zeroDivZero] using divide_zero_raw 0

/-- `0 / 0` is not an embedded ordinary natural number. -/
theorem zeroDivZero_ne_old (c : Nat) :
    zeroDivZero ≠ old c := by
  intro h
  have hraw := congrArg Subtype.val h
  rw [zeroDivZero_raw, old_val] at hraw
  cases hraw

/-- `0 / 0` and `1 / 0` are distinct structured Answers. -/
theorem zeroDivZero_ne_oneDivZero :
    zeroDivZero ≠ divide 1 0 := by
  intro h
  have hnum : (0 : Nat) = 1 :=
    divide_zero_injective (by simpa [zeroDivZero] using h)
  exact Nat.zero_ne_one hnum

/-- A nested singular computation: add one after evaluating `0 / 0`. -/
noncomputable def addOneAfterZeroDivZero : Answer :=
  Free.generatedOp alg Op.add zeroDivZero (old 1)

/-- Nested singular calculations preserve their complete operation tree. -/
@[simp] theorem addOneAfterZeroDivZero_raw :
    addOneAfterZeroDivZero.1 =
      RawAns.susp Op.add
        (RawAns.susp Op.div
          (RawAns.old (0 : Nat)) (RawAns.old (0 : Nat)))
        (RawAns.old (1 : Nat)) := by
  unfold addOneAfterZeroDivZero
  rw [Free.generatedOp_val, zeroDivZero_raw, old_val]
  rfl

/-- The generic completed carrier specialized to concrete arithmetic. -/
abbrev Completion :=
  Filtered.Completion (generatedFilteredSpace alg)

/-- Embed a generated arithmetic Answer into the completed carrier. -/
def embedAnswer (x : Answer) : Completion :=
  Filtered.embed (generatedFilteredSpace alg) x

/-- Embed an ordinary natural number into the completed carrier. -/
def embedNat (a : Nat) : Completion :=
  embedAnswer (old a)

/-- Total completed division. It is defined for every pair of completed
    arithmetic Answers. -/
noncomputable def completedDivide
    (q r : Completion) : Completion :=
  completedGeneratedOp alg Op.div q r

/-- Completed division extends generated division on old natural numbers. -/
theorem completedDivide_embedNat (a b : Nat) :
    completedDivide (embedNat a) (embedNat b) =
      embedAnswer (divide a b) := by
  simpa [completedDivide, embedNat, embedAnswer, divide, old] using
    (completedGeneratedOp_embed alg Op.div
      (Free.generatedOld alg a) (Free.generatedOld alg b))

/-- Completed division by zero returns the embedded structured singular
    Answer. -/
theorem completedDivide_by_zero (a : Nat) :
    completedDivide (embedNat a) (embedNat 0) =
      embedAnswer (divide a 0) :=
  completedDivide_embedNat a 0

/-- Completed division agrees with ordinary division away from zero. -/
theorem completedDivide_of_ne_zero
    (a b : Nat) (hb : b ≠ 0) :
    completedDivide (embedNat a) (embedNat b) =
      embedNat (a / b) := by
  calc
    completedDivide (embedNat a) (embedNat b) =
        embedAnswer (divide a b) :=
      completedDivide_embedNat a b
    _ = embedNat (a / b) := by
      simp [embedNat, divide_normalizes_of_ne_zero a b hb]

/-- The completed value of `0 / 0`. -/
noncomputable def completedZeroDivZero : Completion :=
  completedDivide (embedNat 0) (embedNat 0)

/-- Completed `0 / 0` is exactly the completion embedding of the generated
    suspended `0 / 0` Answer. -/
theorem completedZeroDivZero_eq :
    completedZeroDivZero = embedAnswer zeroDivZero := by
  simpa [completedZeroDivZero, zeroDivZero] using
    (completedDivide_embedNat 0 0)

/-- Completed `0 / 0` is not any embedded ordinary natural number. -/
theorem completedZeroDivZero_ne_old (c : Nat) :
    completedZeroDivZero ≠ embedNat c := by
  intro h
  rw [completedZeroDivZero_eq] at h
  have hGenerated : zeroDivZero = old c := by
    apply Filtered.embed_injective (generatedFilteredSpace alg)
    simpa [embedAnswer, embedNat] using h
  exact zeroDivZero_ne_old c hGenerated

/-- Completed `0 / 0` remains distinct from completed `1 / 0`. -/
theorem completedZeroDivZero_ne_oneDivZero :
    completedZeroDivZero ≠
      completedDivide (embedNat 1) (embedNat 0) := by
  intro h
  rw [completedZeroDivZero_eq, completedDivide_embedNat] at h
  have hGenerated : zeroDivZero = divide 1 0 := by
    apply Filtered.embed_injective (generatedFilteredSpace alg)
    simpa [embedAnswer] using h
  exact zeroDivZero_ne_oneDivZero hGenerated

/-- Explicit totality witness for completed arithmetic division. -/
theorem completedDivision_has_answer
    (q r : Completion) :
    ∃ z : Completion, completedDivide q r = z :=
  ⟨completedDivide q r, rfl⟩

end NatArithmetic
end External

namespace External

variable {Sigma : Signature.{u}}
end External

namespace External
namespace NatArithmetic

/-- Every generated division-by-zero Answer lies outside the embedded old
    natural-number fragment. -/
theorem divide_zero_ne_old (a c : Nat) :
    divide a 0 ≠ old c := by
  intro h
  have hraw := congrArg Subtype.val h
  rw [divide_zero_raw, old_val] at hraw
  cases hraw

/-- The completed arithmetic carrier contains no collision between a singular
    division-by-zero Answer and an embedded ordinary natural number. -/
theorem completedDivide_zero_ne_old (a c : Nat) :
    completedDivide (embedNat a) (embedNat 0) ≠ embedNat c := by
  intro h
  rw [completedDivide_by_zero] at h
  have hGenerated : divide a 0 = old c := by
    apply Filtered.embed_injective (generatedFilteredSpace alg)
    simpa [embedAnswer, embedNat] using h
  exact divide_zero_ne_old a c hGenerated

/-- Distinct numerators give distinct completed division-by-zero Answers. -/
theorem completedDivide_zero_injective :
    Function.Injective
      (fun a : Nat => completedDivide (embedNat a) (embedNat 0)) := by
  intro a b hab
  change completedDivide (embedNat a) (embedNat 0) =
      completedDivide (embedNat b) (embedNat 0) at hab
  rw [completedDivide_by_zero a, completedDivide_by_zero b] at hab
  apply divide_zero_injective
  apply Filtered.embed_injective (generatedFilteredSpace alg)
  simpa [embedAnswer] using hab

/-- Total completed addition on arithmetic completion points. -/
noncomputable def completedAdd
    (q r : Completion) : Completion :=
  completedGeneratedOp alg Op.add q r

/-- Total completed multiplication on arithmetic completion points. -/
noncomputable def completedMultiply
    (q r : Completion) : Completion :=
  completedGeneratedOp alg Op.mul q r

/-- Completed addition agrees exactly with ordinary addition on embedded
    natural numbers. -/
theorem completedAdd_embedNat (a b : Nat) :
    completedAdd (embedNat a) (embedNat b) =
      embedNat (a + b) := by
  calc
    completedAdd (embedNat a) (embedNat b) =
        embedAnswer (add a b) := by
      simpa [completedAdd, embedNat, embedAnswer, add, old] using
        (completedGeneratedOp_embed alg Op.add
          (Free.generatedOld alg a) (Free.generatedOld alg b))
    _ = embedNat (a + b) := by
      rw [add_normalizes]
      rfl

/-- Completed multiplication agrees exactly with ordinary multiplication on
    embedded natural numbers. -/
theorem completedMultiply_embedNat (a b : Nat) :
    completedMultiply (embedNat a) (embedNat b) =
      embedNat (a * b) := by
  calc
    completedMultiply (embedNat a) (embedNat b) =
        embedAnswer (multiply a b) := by
      simpa [completedMultiply, embedNat, embedAnswer, multiply, old] using
        (completedGeneratedOp_embed alg Op.mul
          (Free.generatedOld alg a) (Free.generatedOld alg b))
    _ = embedNat (a * b) := by
      rw [multiply_normalizes]
      rfl

/-- Ordinary natural numbers remain injectively embedded in the completed
    arithmetic carrier. -/
theorem embedNat_injective : Function.Injective embedNat := by
  intro a b hab
  apply Free.generatedOld_injective alg
  apply Filtered.embed_injective (generatedFilteredSpace alg)
  simpa [embedNat, embedAnswer, old] using hab

/-- In particular, the completed arithmetic carrier does not identify zero and
    one. -/
theorem embedNat_zero_ne_one : embedNat 0 ≠ embedNat 1 := by
  intro h
  exact Nat.zero_ne_one (embedNat_injective h)

/-- Compact conservativity package for ordinary arithmetic: addition and
    multiplication are unchanged, and division is unchanged whenever its old
    denominator is nonzero. -/
theorem completedArithmetic_conservative :
    (∀ a b : Nat,
      completedAdd (embedNat a) (embedNat b) = embedNat (a + b)) ∧
    (∀ a b : Nat,
      completedMultiply (embedNat a) (embedNat b) = embedNat (a * b)) ∧
    (∀ a b : Nat, b ≠ 0 →
      completedDivide (embedNat a) (embedNat b) = embedNat (a / b)) := by
  constructor
  · exact completedAdd_embedNat
  · constructor
    · exact completedMultiply_embedNat
    · exact completedDivide_of_ne_zero

/-- Four fresh semantic tags suffice to separate concrete `0 / 0` from any
    embedded ordinary natural number. -/
theorem zeroDivZero_separated_at_four_tags (c : Nat) :
    FiniteTagSeparatesAt alg zeroDivZero (old c) 4 := by
  have h := finiteTagSeparatesAt_size_bound
    alg zeroDivZero (old c) (zeroDivZero_ne_old c)
  simpa [FiniteTagProof.nodeCount] using h

/-- Six fresh semantic tags suffice to separate `0 / 0` from `1 / 0`. -/
theorem zeroDivZero_separated_from_oneDivZero_at_six_tags :
    FiniteTagSeparatesAt alg zeroDivZero (divide 1 0) 6 := by
  have h := finiteTagSeparatesAt_size_bound
    alg zeroDivZero (divide 1 0) zeroDivZero_ne_oneDivZero
  change FiniteTagSeparatesAt alg zeroDivZero (divide 1 0)
    (FiniteTagProof.nodeCount alg zeroDivZero.1 +
      FiniteTagProof.nodeCount alg (divide 1 0).1) at h
  rw [zeroDivZero_raw, divide_zero_raw] at h
  simpa [FiniteTagProof.nodeCount] using h

/-- The concrete finite separation rank of `0 / 0` from an old value is bounded
    by four. -/
theorem zeroDivZero_rank_le_four (c : Nat) :
    finiteSeparationRank alg zeroDivZero (old c) ≤ 4 := by
  have h := finiteSeparationRank_le_size
    alg (zeroDivZero_ne_old c)
  simpa [FiniteTagProof.nodeCount] using h

/-- The concrete finite separation rank between `0 / 0` and `1 / 0` is bounded
    by six. -/
theorem zeroDivZero_oneDivZero_rank_le_six :
    finiteSeparationRank alg zeroDivZero (divide 1 0) ≤ 6 := by
  have h := finiteSeparationRank_le_size
    alg zeroDivZero_ne_oneDivZero
  change finiteSeparationRank alg zeroDivZero (divide 1 0) ≤
    FiniteTagProof.nodeCount alg zeroDivZero.1 +
      FiniteTagProof.nodeCount alg (divide 1 0).1 at h
  rw [zeroDivZero_raw, divide_zero_raw] at h
  simpa [FiniteTagProof.nodeCount] using h

/-- Explicit external-model form of the four-tag separator. -/
theorem zeroDivZero_has_four_tag_external_model (c : Nat) :
    ∃ T : FiniteTagAlg alg 4,
      Free.TotalAlg.interp alg (T.toTotalAlg alg) zeroDivZero ≠
        Free.TotalAlg.interp alg (T.toTotalAlg alg) (old c) := by
  simpa [FiniteTagSeparatesAt] using
    zeroDivZero_separated_at_four_tags c

/-- The arithmetic instance simultaneously preserves ordinary arithmetic and
    keeps the entire division-by-zero family structurally distinct. -/
theorem arithmetic_totality_without_old_collapse :
    Function.Injective embedNat ∧
    Function.Injective
      (fun a : Nat => completedDivide (embedNat a) (embedNat 0)) ∧
    (∀ a c : Nat,
      completedDivide (embedNat a) (embedNat 0) ≠ embedNat c) := by
  exact ⟨embedNat_injective, completedDivide_zero_injective,
    completedDivide_zero_ne_old⟩

end NatArithmetic
end External

namespace External

variable {Sigma : Signature.{u}}
end External

universe r

/-- Algebraic terms with variables, named old-carrier constants, and the binary
    Resolution operations. -/
inductive ConstantAlgebraTerm
    (Sigma : Signature.{u}) (A : Type r) (V : Type q) where
  | var : V -> ConstantAlgebraTerm Sigma A V
  | const : A -> ConstantAlgebraTerm Sigma A V
  | app : Sigma.Op ->
      ConstantAlgebraTerm Sigma A V ->
      ConstantAlgebraTerm Sigma A V ->
      ConstantAlgebraTerm Sigma A V

/-- One equation between constant-bearing algebraic terms. -/
abbrev ConstantEquation
    (Sigma : Signature.{u}) (A : Type r) (V : Type q) :=
  ConstantAlgebraTerm Sigma A V × ConstantAlgebraTerm Sigma A V

namespace ConstantAlgebraTerm

variable {Sigma : Signature.{u}}
variable {V : Type q}

/-- Evaluate a constant-bearing term in the generated Resolution algebra. -/
noncomputable def evalGenerated
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D) :
    ConstantAlgebraTerm Sigma D.Carrier V -> Free.GeneratedAns D
  | .var x => rho x
  | .const a => Free.generatedOld D a
  | .app f s t =>
      Free.generatedOp D f
        (evalGenerated D rho s)
        (evalGenerated D rho t)

@[simp] theorem evalGenerated_var
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (x : V) :
    evalGenerated D rho (.var x) = rho x := by
  rfl

@[simp] theorem evalGenerated_const
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (a : D.Carrier) :
    evalGenerated D rho (.const a) = Free.generatedOld D a := by
  rfl

@[simp] theorem evalGenerated_app
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (f : Sigma.Op)
    (s t : ConstantAlgebraTerm Sigma D.Carrier V) :
    evalGenerated D rho (.app f s t) =
      Free.generatedOp D f
        (evalGenerated D rho s)
        (evalGenerated D rho t) := by
  rfl

end ConstantAlgebraTerm

namespace External

variable {Sigma : Signature.{u}}
variable {V : Type q}

/-- Evaluate a constant-bearing term in the canonical completed Resolution
    algebra. -/
noncomputable def ConstantAlgebraTerm.evalCompleted
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D)) :
    ConstantAlgebraTerm Sigma D.Carrier V ->
      Filtered.Completion (generatedFilteredSpace D)
  | .var x => rho x
  | .const a =>
      Filtered.embed (generatedFilteredSpace D) (Free.generatedOld D a)
  | .app f s t =>
      completedGeneratedOp D f
        (ConstantAlgebraTerm.evalCompleted D rho s)
        (ConstantAlgebraTerm.evalCompleted D rho t)

@[simp] theorem ConstantAlgebraTerm.evalCompleted_var
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (x : V) :
    ConstantAlgebraTerm.evalCompleted D rho (.var x) = rho x := by
  rfl

@[simp] theorem ConstantAlgebraTerm.evalCompleted_const
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (a : D.Carrier) :
    ConstantAlgebraTerm.evalCompleted D rho (.const a) =
      Filtered.embed (generatedFilteredSpace D) (Free.generatedOld D a) := by
  rfl

@[simp] theorem ConstantAlgebraTerm.evalCompleted_app
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (f : Sigma.Op)
    (s t : ConstantAlgebraTerm Sigma D.Carrier V) :
    ConstantAlgebraTerm.evalCompleted D rho (.app f s t) =
      completedGeneratedOp D f
        (ConstantAlgebraTerm.evalCompleted D rho s)
        (ConstantAlgebraTerm.evalCompleted D rho t) := by
  rfl

/-- Evaluation on embedded generated assignments is exactly the embedding of
    generated evaluation, including all named old constants. -/
theorem ConstantAlgebraTerm.evalCompleted_embed
    (D : PartialAlg.{u,v} Sigma)
    (rho : V -> Free.GeneratedAns D)
    (t : ConstantAlgebraTerm Sigma D.Carrier V) :
    ConstantAlgebraTerm.evalCompleted D
        (fun x => Filtered.embed (generatedFilteredSpace D) (rho x)) t =
      Filtered.embed (generatedFilteredSpace D)
        (ConstantAlgebraTerm.evalGenerated D rho t) := by
  induction t with
  | var x =>
      rfl
  | const a =>
      rfl
  | app f s t ihs iht =>
      simp only [ConstantAlgebraTerm.evalCompleted_app,
        ConstantAlgebraTerm.evalGenerated_app]
      rw [ihs, iht]
      exact completedGeneratedOp_embed D f
        (ConstantAlgebraTerm.evalGenerated D rho s)
        (ConstantAlgebraTerm.evalGenerated D rho t)

/-- Every constant-bearing term is finite-stage compatible in all variables. -/
theorem ConstantAlgebraTerm.evalCompleted_map_eqAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (rho sigma : V -> Filtered.Completion (generatedFilteredSpace D))
    (t : ConstantAlgebraTerm Sigma D.Carrier V)
    (hvars : forall x : V,
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (rho x) (sigma x)) :
    Filtered.CompletionEqAt (generatedFilteredSpace D) n
      (ConstantAlgebraTerm.evalCompleted D rho t)
      (ConstantAlgebraTerm.evalCompleted D sigma t) := by
  induction t with
  | var x =>
      exact hvars x
  | const a =>
      exact Filtered.completionEqAt_refl
        (generatedFilteredSpace D) n _
  | app f s t ihs iht =>
      simp only [ConstantAlgebraTerm.evalCompleted_app]
      exact completedGeneratedOp_preserves_eqAt D f n ihs iht

/-- Fixed-stage validity of a list of premises in the generated Resolution
    algebra. -/
def GeneratedPremisesAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (rho : V -> Free.GeneratedAns D)
    (premises : List (ConstantEquation Sigma D.Carrier V)) : Prop :=
  forall e : ConstantEquation Sigma D.Carrier V, e ∈ premises ->
    FiniteObservationBall D n
      (ConstantAlgebraTerm.evalGenerated D rho e.1)
      (ConstantAlgebraTerm.evalGenerated D rho e.2)

/-- Fixed-stage validity of a list of premises in the completed algebra. -/
def CompletedPremisesAt
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (rho : V -> Filtered.Completion (generatedFilteredSpace D))
    (premises : List (ConstantEquation Sigma D.Carrier V)) : Prop :=
  forall e : ConstantEquation Sigma D.Carrier V, e ∈ premises ->
    Filtered.CompletionEqAt (generatedFilteredSpace D) n
      (ConstantAlgebraTerm.evalCompleted D rho e.1)
      (ConstantAlgebraTerm.evalCompleted D rho e.2)

/-- A guarded equation valid at one finite stage in the generated algebra. -/
def GeneratedStageConditional
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V) : Prop :=
  forall rho : V -> Free.GeneratedAns D,
    GeneratedPremisesAt D n rho premises ->
      FiniteObservationBall D n
        (ConstantAlgebraTerm.evalGenerated D rho lhs)
        (ConstantAlgebraTerm.evalGenerated D rho rhs)

/-- The corresponding guarded equation at one finite stage in the completed
    algebra. -/
def CompletedStageConditional
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V) : Prop :=
  forall rho : V -> Filtered.Completion (generatedFilteredSpace D),
    CompletedPremisesAt D n rho premises ->
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (ConstantAlgebraTerm.evalCompleted D rho lhs)
        (ConstantAlgebraTerm.evalCompleted D rho rhs)

/-- Robust guarded laws transfer from the dense generated algebra to the
    completion at every fixed finite stage. -/
theorem generatedStageConditional_transfers_to_completion
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V)
    (hGenerated : GeneratedStageConditional D n premises lhs rhs) :
    CompletedStageConditional D n premises lhs rhs := by
  intro rho hPremises
  let approx : V -> Free.GeneratedAns D :=
    completionAssignmentApprox D n rho
  have hApprox : forall x : V,
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (rho x)
        (Filtered.embed (generatedFilteredSpace D) (approx x)) := by
    intro x
    exact completionAssignmentApprox_spec D n rho x
  have hGeneratedPremises :
      GeneratedPremisesAt D n approx premises := by
    intro e he
    have hLeft := ConstantAlgebraTerm.evalCompleted_map_eqAt
      D n rho
      (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
      e.1 hApprox
    have hRight := ConstantAlgebraTerm.evalCompleted_map_eqAt
      D n rho
      (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
      e.2 hApprox
    have hMiddle := hPremises e he
    have hDense :
        Filtered.CompletionEqAt (generatedFilteredSpace D) n
          (ConstantAlgebraTerm.evalCompleted D
            (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
            e.1)
          (ConstantAlgebraTerm.evalCompleted D
            (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
            e.2) :=
      Filtered.completionEqAt_trans (generatedFilteredSpace D) n
        (Filtered.completionEqAt_symm (generatedFilteredSpace D) n hLeft)
        (Filtered.completionEqAt_trans (generatedFilteredSpace D) n
          hMiddle hRight)
    rw [ConstantAlgebraTerm.evalCompleted_embed D approx e.1,
      ConstantAlgebraTerm.evalCompleted_embed D approx e.2] at hDense
    exact (Filtered.completionEqAt_embed_iff
      (generatedFilteredSpace D) n _ _).1 hDense
  have hGeneratedConclusion := hGenerated approx hGeneratedPremises
  have hLeft := ConstantAlgebraTerm.evalCompleted_map_eqAt
    D n rho
    (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
    lhs hApprox
  have hRight := ConstantAlgebraTerm.evalCompleted_map_eqAt
    D n rho
    (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
    rhs hApprox
  have hDenseConclusion :
      Filtered.CompletionEqAt (generatedFilteredSpace D) n
        (ConstantAlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          lhs)
        (ConstantAlgebraTerm.evalCompleted D
          (fun x => Filtered.embed (generatedFilteredSpace D) (approx x))
          rhs) := by
    rw [ConstantAlgebraTerm.evalCompleted_embed D approx lhs,
      ConstantAlgebraTerm.evalCompleted_embed D approx rhs]
    exact (Filtered.completionEqAt_embed_iff
      (generatedFilteredSpace D) n _ _).2 hGeneratedConclusion
  exact Filtered.completionEqAt_trans (generatedFilteredSpace D) n
    hLeft
    (Filtered.completionEqAt_trans (generatedFilteredSpace D) n
      hDenseConclusion
      (Filtered.completionEqAt_symm (generatedFilteredSpace D) n hRight))

/-- Fixed-stage guarded validity also reflects from the completion to the
    generated algebra. -/
theorem completedStageConditional_reflects_to_generated
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V)
    (hCompleted : CompletedStageConditional D n premises lhs rhs) :
    GeneratedStageConditional D n premises lhs rhs := by
  intro rho hPremises
  have hCompletedPremises : CompletedPremisesAt D n
      (fun x => Filtered.embed (generatedFilteredSpace D) (rho x))
      premises := by
    intro e he
    rw [ConstantAlgebraTerm.evalCompleted_embed D rho e.1,
      ConstantAlgebraTerm.evalCompleted_embed D rho e.2]
    exact (Filtered.completionEqAt_embed_iff
      (generatedFilteredSpace D) n _ _).2 (hPremises e he)
  have hConclusion := hCompleted
    (fun x => Filtered.embed (generatedFilteredSpace D) (rho x))
    hCompletedPremises
  rw [ConstantAlgebraTerm.evalCompleted_embed D rho lhs,
    ConstantAlgebraTerm.evalCompleted_embed D rho rhs] at hConclusion
  exact (Filtered.completionEqAt_embed_iff
    (generatedFilteredSpace D) n _ _).1 hConclusion

/-- Exact fixed-stage conservativity for robust guarded equations. -/
theorem completedStageConditional_iff_generatedStageConditional
    (D : PartialAlg.{u,v} Sigma)
    (n : Nat)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V) :
    CompletedStageConditional D n premises lhs rhs <->
      GeneratedStageConditional D n premises lhs rhs := by
  constructor
  · exact completedStageConditional_reflects_to_generated
      D n premises lhs rhs
  · exact generatedStageConditional_transfers_to_completion
      D n premises lhs rhs

/-- Stagewise robust guarded validity in the generated algebra. -/
def GeneratedStagewiseConditional
    (D : PartialAlg.{u,v} Sigma)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V) : Prop :=
  forall n : Nat, GeneratedStageConditional D n premises lhs rhs

/-- Exact conditional validity in the completed algebra. -/
def CompletedExactConditional
    (D : PartialAlg.{u,v} Sigma)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V) : Prop :=
  forall rho : V -> Filtered.Completion (generatedFilteredSpace D),
    (forall e : ConstantEquation Sigma D.Carrier V, e ∈ premises ->
      ConstantAlgebraTerm.evalCompleted D rho e.1 =
        ConstantAlgebraTerm.evalCompleted D rho e.2) ->
      ConstantAlgebraTerm.evalCompleted D rho lhs =
        ConstantAlgebraTerm.evalCompleted D rho rhs

/-- If a guarded law is valid robustly at every finite observational stage in
    the generated algebra, then it is exactly valid in the completion whenever
    its premises hold exactly. This is the safe conditional-transfer theorem. -/
theorem stagewiseGeneratedConditional_transfers_to_exactCompletion
    (D : PartialAlg.{u,v} Sigma)
    (premises : List (ConstantEquation Sigma D.Carrier V))
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V)
    (hStagewise : GeneratedStagewiseConditional D premises lhs rhs) :
    CompletedExactConditional D premises lhs rhs := by
  intro rho hPremises
  apply (Filtered.forall_completionEqAt_iff_eq
    (generatedFilteredSpace D)
    (ConstantAlgebraTerm.evalCompleted D rho lhs)
    (ConstantAlgebraTerm.evalCompleted D rho rhs)).1
  intro n
  apply generatedStageConditional_transfers_to_completion
    D n premises lhs rhs (hStagewise n) rho
  intro e he
  simpa [hPremises e he] using
    (Filtered.completionEqAt_refl
      (generatedFilteredSpace D) n
      (ConstantAlgebraTerm.evalCompleted D rho e.2))

/-- Unconditional equations with named constants transfer exactly to the
    completion. -/
theorem generatedConstantEquation_transfers_to_completion
    (D : PartialAlg.{u,v} Sigma)
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V)
    (hGenerated : forall rho : V -> Free.GeneratedAns D,
      ConstantAlgebraTerm.evalGenerated D rho lhs =
        ConstantAlgebraTerm.evalGenerated D rho rhs) :
    forall rho : V -> Filtered.Completion (generatedFilteredSpace D),
      ConstantAlgebraTerm.evalCompleted D rho lhs =
        ConstantAlgebraTerm.evalCompleted D rho rhs := by
  have hStagewise : GeneratedStagewiseConditional D [] lhs rhs := by
    intro n rho hEmpty
    simpa [hGenerated rho] using
      (finiteObservationBall_center D n
        (ConstantAlgebraTerm.evalGenerated D rho rhs))
  have hExact := stagewiseGeneratedConditional_transfers_to_exactCompletion
    D [] lhs rhs hStagewise
  intro rho
  exact hExact rho (by
    intro e he
    simp at he)

/-- Exact equational conservativity remains true after adding named old
    constants to the term language. -/
theorem completionConstantEquation_iff_generatedConstantEquation
    (D : PartialAlg.{u,v} Sigma)
    (lhs rhs : ConstantAlgebraTerm Sigma D.Carrier V) :
    (forall rho : V -> Filtered.Completion (generatedFilteredSpace D),
      ConstantAlgebraTerm.evalCompleted D rho lhs =
        ConstantAlgebraTerm.evalCompleted D rho rhs) <->
    (forall rho : V -> Free.GeneratedAns D,
      ConstantAlgebraTerm.evalGenerated D rho lhs =
        ConstantAlgebraTerm.evalGenerated D rho rhs) := by
  constructor
  · intro hCompleted rho
    apply Filtered.embed_injective (generatedFilteredSpace D)
    have h := hCompleted
      (fun x => Filtered.embed (generatedFilteredSpace D) (rho x))
    rw [ConstantAlgebraTerm.evalCompleted_embed D rho lhs,
      ConstantAlgebraTerm.evalCompleted_embed D rho rhs] at h
    exact h
  · exact generatedConstantEquation_transfers_to_completion D lhs rhs

namespace NatArithmetic

/-- Constant-bearing arithmetic terms. -/
abbrev ConstantTerm (V : Type q) :=
  ConstantAlgebraTerm signature Nat V

/-- Ground numeral zero. -/
def zeroTerm (V : Type q) : ConstantTerm V :=
  .const 0

/-- Ground numeral one. -/
def oneTerm (V : Type q) : ConstantTerm V :=
  .const 1

/-- Ground term representing `0 / 0`. -/
def zeroDivZeroTerm (V : Type q) : ConstantTerm V :=
  .app Op.div (zeroTerm V) (zeroTerm V)

@[simp] theorem evalGenerated_zeroTerm
    (rho : Unit -> Answer) :
    ConstantAlgebraTerm.evalGenerated alg rho (zeroTerm Unit) = old 0 := by
  rfl

@[simp] theorem evalGenerated_zeroDivZeroTerm
    (rho : Unit -> Answer) :
    ConstantAlgebraTerm.evalGenerated alg rho (zeroDivZeroTerm Unit) =
      zeroDivZero := by
  rfl

@[simp] theorem evalCompleted_zeroTerm
    (rho : Unit -> Completion) :
    ConstantAlgebraTerm.evalCompleted alg rho (zeroTerm Unit) =
      embedNat 0 := by
  rfl

@[simp] theorem evalCompleted_zeroDivZeroTerm
    (rho : Unit -> Completion) :
    ConstantAlgebraTerm.evalCompleted alg rho (zeroDivZeroTerm Unit) =
      completedZeroDivZero := by
  rfl

/-- The named-constant language records concretely that the ground equation
    `0 / 0 = 0` fails in the completed arithmetic algebra. -/
theorem zeroDivZero_ground_equation_fails :
    ¬ (forall rho : Unit -> Completion,
      ConstantAlgebraTerm.evalCompleted alg rho (zeroDivZeroTerm Unit) =
        ConstantAlgebraTerm.evalCompleted alg rho (zeroTerm Unit)) := by
  intro h
  have hBad := h (fun _ => embedNat 0)
  rw [evalCompleted_zeroDivZeroTerm, evalCompleted_zeroTerm] at hBad
  exact completedZeroDivZero_ne_old 0 hBad

end NatArithmetic

end External

namespace External

variable {Sigma : Signature.{u}}
end External

namespace External
namespace NatArithmetic

/-- A completion point belongs to the old arithmetic fragment when it is the
    image of an ordinary natural number. -/
def IsOldCompletion (q : Completion) : Prop :=
  ∃ a : Nat, q = embedNat a

/-- Equality of embedded old natural numbers is exactly ordinary equality. -/
theorem embedNat_eq_iff (a b : Nat) :
    embedNat a = embedNat b ↔ a = b := by
  constructor
  · intro h
    exact embedNat_injective h
  · intro h
    exact congrArg embedNat h

/-- An old representation, when it exists, is unique. -/
theorem oldCompletion_representation_unique
    {q : Completion} {a b : Nat}
    (ha : q = embedNat a)
    (hb : q = embedNat b) : a = b := by
  apply embedNat_injective
  exact ha.symm.trans hb

/-- Completed addition reflects ordinary arithmetic equality exactly. -/
theorem completedAdd_eq_embedNat_iff
    (a b c : Nat) :
    completedAdd (embedNat a) (embedNat b) = embedNat c ↔
      a + b = c := by
  rw [completedAdd_embedNat]
  exact embedNat_eq_iff (a + b) c

/-- Completed multiplication reflects ordinary arithmetic equality exactly. -/
theorem completedMultiply_eq_embedNat_iff
    (a b c : Nat) :
    completedMultiply (embedNat a) (embedNat b) = embedNat c ↔
      a * b = c := by
  rw [completedMultiply_embedNat]
  exact embedNat_eq_iff (a * b) c

/-- Away from denominator zero, completed division reflects ordinary
    natural-number division equality exactly. -/
theorem completedDivide_eq_embedNat_iff_of_ne_zero
    (a b c : Nat) (hb : b ≠ 0) :
    completedDivide (embedNat a) (embedNat b) = embedNat c ↔
      a / b = c := by
  rw [completedDivide_of_ne_zero a b hb]
  exact embedNat_eq_iff (a / b) c

/-- No completed division-by-zero result belongs to the old arithmetic
    fragment. -/
theorem completedDivide_zero_not_old (a : Nat) :
    ¬ IsOldCompletion
      (completedDivide (embedNat a) (embedNat 0)) := by
  rintro ⟨c, hc⟩
  exact completedDivide_zero_ne_old a c hc

/-- In particular, completed `0 / 0` is genuinely outside the old fragment. -/
theorem completedZeroDivZero_not_old :
    ¬ IsOldCompletion completedZeroDivZero := by
  rintro ⟨c, hc⟩
  exact completedZeroDivZero_ne_old c hc

/-- Equality inside the completed division-by-zero family is exactly equality
    of numerators. -/
theorem completedDivide_zero_eq_iff
    (a b : Nat) :
    completedDivide (embedNat a) (embedNat 0) =
        completedDivide (embedNat b) (embedNat 0) ↔
      a = b := by
  constructor
  · intro h
    exact completedDivide_zero_injective h
  · intro h
    exact congrArg
      (fun x : Nat => completedDivide (embedNat x) (embedNat 0)) h

/-- The completed arithmetic carrier is nontrivial. -/
theorem arithmeticCompletion_nontrivial :
    ∃ x y : Completion, x ≠ y :=
  ⟨embedNat 0, embedNat 1, embedNat_zero_ne_one⟩

/-- The completed arithmetic total algebra is a concrete compatible model of
    the original partial arithmetic operations. -/
noncomputable def completedArithmeticModel : Free.TotalAlg alg :=
  completedResolutionTotalAlg alg

/-- The model embeds old naturals injectively. -/
theorem completedArithmeticModel_embed_injective :
    Function.Injective completedArithmeticModel.embed :=
  completedArithmeticModel.embed_injective

/-- The model preserves every operation that was already defined in the old
    partial arithmetic algebra. -/
theorem completedArithmeticModel_preserves_defined
    (f : Op) (a b c : Nat)
    (h : eval f a b = some c) :
    completedArithmeticModel.op f
        (completedArithmeticModel.embed a)
        (completedArithmeticModel.embed b) =
      completedArithmeticModel.embed c :=
  completedArithmeticModel.preserve f a b c h

/-- Exact old-fragment conservativity and singular noncollapse, collected as a
    single theorem package for the concrete arithmetic model. -/
theorem arithmetic_relative_noncollapse :
    (∀ a b : Nat, embedNat a = embedNat b ↔ a = b) ∧
    (∀ a b c : Nat,
      completedAdd (embedNat a) (embedNat b) = embedNat c ↔
        a + b = c) ∧
    (∀ a b c : Nat,
      completedMultiply (embedNat a) (embedNat b) = embedNat c ↔
        a * b = c) ∧
    (∀ a b c : Nat, b ≠ 0 →
      (completedDivide (embedNat a) (embedNat b) = embedNat c ↔
        a / b = c)) ∧
    (∀ a : Nat,
      ¬ IsOldCompletion
        (completedDivide (embedNat a) (embedNat 0))) ∧
    (∃ x y : Completion, x ≠ y) := by
  exact ⟨embedNat_eq_iff,
    completedAdd_eq_embedNat_iff,
    completedMultiply_eq_embedNat_iff,
    completedDivide_eq_embedNat_iff_of_ne_zero,
    completedDivide_zero_not_old,
    arithmeticCompletion_nontrivial⟩

/-- There are infinitely many pairwise distinguished singular completion
    points, indexed injectively by the old natural-number numerators, and none
    lies in the old image. -/
theorem infinite_singular_family :
    Function.Injective
      (fun a : Nat => completedDivide (embedNat a) (embedNat 0)) ∧
    (∀ a : Nat,
      ¬ IsOldCompletion
        (completedDivide (embedNat a) (embedNat 0))) :=
  ⟨completedDivide_zero_injective, completedDivide_zero_not_old⟩

end NatArithmetic
end External

namespace External

variable {Sigma : Signature.{u}}

/-- External finite-tag observational completeness, with separation discharged. -/
theorem finiteTag_full_abstraction_verified (D : PartialAlg Sigma)
    (x y : Free.GeneratedAns D) :
    FiniteTagEq D x y <-> x = y :=
  finiteTag_full_abstraction D (finiteTagSeparating_theorem D) x y

end External
end Resolution
