import ResolutionFiniteTagProof

/-!
# Relative finite-pattern realization

The pair-dependent separator in `ResolutionFiniteTagProof` uses the finite list
of subterms of two roots.  This module replaces that pair-specific selected
list by the finite subterm closure of an arbitrary finite list of roots.

The construction still fixes the entire partial base pointwise.  Only selected
suspended nodes receive finite tags; all unselected transitions go to one
overflow state.  Hence one compatible total observer evaluates every selected
normal node to an injective finite encoding, simultaneously realizing any
finite pattern of generated Answers.
-/

universe u v

namespace Resolution
namespace External
namespace FinitePatternRealization

open FiniteTagProof

variable {Sigma : Signature.{u}}
variable (D : PartialAlg.{u,v} Sigma)

/-- Finite subterm closure of an arbitrary finite list of roots. -/
def patternSelected :
    List (RawAns Sigma D.Carrier) -> List (RawAns Sigma D.Carrier)
  | [] => []
  | r :: rs => subterms D r ++ patternSelected rs

@[simp] theorem patternSelected_nil :
    patternSelected D ([] : List (RawAns Sigma D.Carrier)) = [] := rfl

@[simp] theorem patternSelected_cons
    (r : RawAns Sigma D.Carrier)
    (rs : List (RawAns Sigma D.Carrier)) :
    patternSelected D (r :: rs) = subterms D r ++ patternSelected D rs := rfl

/-- Every root belongs to the selected finite closure. -/
theorem root_mem_patternSelected
    {r : RawAns Sigma D.Carrier}
    {roots : List (RawAns Sigma D.Carrier)}
    (hr : r ∈ roots) : r ∈ patternSelected D roots := by
  induction roots with
  | nil => simp at hr
  | cons a roots ih =>
      simp only [List.mem_cons] at hr
      simp only [patternSelected, List.mem_append]
      rcases hr with h | h
      · exact Or.inl (by
          rw [← h]
          exact self_mem_subterms D r)
      · exact Or.inr (ih h)

/-- The arbitrary selected list is closed under children. -/
theorem children_mem_patternSelected
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (h : RawAns.susp f l r ∈ patternSelected D roots) :
    l ∈ patternSelected D roots ∧ r ∈ patternSelected D roots := by
  induction roots with
  | nil => simp [patternSelected] at h
  | cons a roots ih =>
      simp only [patternSelected, List.mem_append] at h ⊢
      rcases h with ha | hs
      · have hc := children_mem_subterms D ha
        exact ⟨Or.inl hc.1, Or.inl hc.2⟩
      · have hc := ih hs
        exact ⟨Or.inr hc.1, Or.inr hc.2⟩

/-- One overflow state for a finite pattern. -/
def patternOverflow
    {roots : List (RawAns Sigma D.Carrier)} :
    FiniteTagCarrier D (patternSelected D roots).length :=
  Sum.inr (Sum.inr ())

/-- Old leaves retain their base value; selected suspensions receive the
first-occurrence tag in the whole finite pattern; everything else overflows. -/
noncomputable def patternEncode
    (roots : List (RawAns Sigma D.Carrier)) :
    RawAns Sigma D.Carrier ->
      FiniteTagCarrier D (patternSelected D roots).length
  | .old a => Sum.inl a
  | t@(.susp _ _ _) => by
      classical
      exact if h : t ∈ patternSelected D roots then
        Sum.inr (Sum.inl (tagIndex t (patternSelected D roots) h))
      else
        patternOverflow D

@[simp] theorem patternEncode_susp_of_mem
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (h : RawAns.susp f l r ∈ patternSelected D roots) :
    patternEncode D roots (RawAns.susp f l r) =
      (Sum.inr (Sum.inl
        (tagIndex (RawAns.susp f l r) (patternSelected D roots) h)) :
          FiniteTagCarrier D (patternSelected D roots).length) := by
  classical
  simp only [patternEncode, dif_pos h]

/-- The pattern encoding is injective on the whole selected finite closure. -/
theorem patternEncode_injective_on
    {roots : List (RawAns Sigma D.Carrier)}
    {s t : RawAns Sigma D.Carrier}
    (hs : s ∈ patternSelected D roots)
    (ht : t ∈ patternSelected D roots)
    (henc : patternEncode D roots s = patternEncode D roots t) : s = t := by
  classical
  cases s with
  | old a =>
      cases t with
      | old b =>
          simp only [patternEncode] at henc
          exact congrArg RawAns.old (Sum.inl.inj henc)
      | susp g l r =>
          simp [patternEncode, ht] at henc
  | susp f l r =>
      cases t with
      | old b =>
          simp [patternEncode, hs] at henc
      | susp g l' r' =>
          have henc' := henc
          rw [patternEncode_susp_of_mem D hs,
            patternEncode_susp_of_mem D ht] at henc'
          have hidx :
              tagIndex (RawAns.susp f l r) (patternSelected D roots) hs =
                tagIndex (RawAns.susp g l' r') (patternSelected D roots) ht := by
            exact Sum.inl.inj (Sum.inr.inj henc')
          exact tagIndex_injective_on hs ht hidx

/-- A selected pattern node matches one table entry. -/
def PatternMatchNode
    (roots : List (RawAns Sigma D.Carrier)) (f : Sigma.Op)
    (p q : FiniteTagCarrier D (patternSelected D roots).length)
    (s : RawAns Sigma D.Carrier) : Prop :=
  match s with
  | .old _ => False
  | .susp g l r =>
      g = f ∧ patternEncode D roots l = p ∧ patternEncode D roots r = q

/-- Finite lookup table for the entire pattern. -/
noncomputable def patternTable
    (roots : List (RawAns Sigma D.Carrier)) (f : Sigma.Op)
    (p q : FiniteTagCarrier D (patternSelected D roots).length) :
    FiniteTagCarrier D (patternSelected D roots).length := by
  classical
  exact if h : Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ patternSelected D roots ∧ PatternMatchNode D roots f p q s then
    patternEncode D roots (Classical.choose h)
  else
    patternOverflow D

/-- Lookup reproduces each selected suspended node. -/
theorem patternTable_hit
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (hs : RawAns.susp f l r ∈ patternSelected D roots) :
    patternTable D roots f (patternEncode D roots l) (patternEncode D roots r) =
      patternEncode D roots (RawAns.susp f l r) := by
  classical
  let hex : Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ patternSelected D roots ∧
        PatternMatchNode D roots f
          (patternEncode D roots l) (patternEncode D roots r) s :=
    ⟨RawAns.susp f l r, hs, by simp [PatternMatchNode]⟩
  unfold patternTable
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have hchosen : Classical.choose hex = RawAns.susp f l r := by
    have hmem := hspec.1
    have hmatch := hspec.2
    cases hval : Classical.choose hex with
    | old a =>
        rw [hval] at hmatch
        simp [PatternMatchNode] at hmatch
    | susp g l' r' =>
        rw [hval] at hmatch hmem
        have hm : g = f ∧
            patternEncode D roots l' = patternEncode D roots l ∧
            patternEncode D roots r' = patternEncode D roots r := by
          simpa only [PatternMatchNode] using hmatch
        have hc' : l' ∈ patternSelected D roots ∧
            r' ∈ patternSelected D roots :=
          children_mem_patternSelected D hmem
        have hc : l ∈ patternSelected D roots ∧
            r ∈ patternSelected D roots :=
          children_mem_patternSelected D hs
        have hl : l' = l :=
          patternEncode_injective_on D hc'.1 hc.1 hm.2.1
        have hr : r' = r :=
          patternEncode_injective_on D hc'.2 hc.2 hm.2.2
        cases hm.1
        cases hl
        cases hr
        rfl
  rw [hchosen]

/-- Conservative total operation for a finite pattern.  Applications already
defined on two base elements are preserved before finite lookup. -/
noncomputable def patternOp
    (roots : List (RawAns Sigma D.Carrier)) (f : Sigma.Op)
    (p q : FiniteTagCarrier D (patternSelected D roots).length) :
    FiniteTagCarrier D (patternSelected D roots).length :=
  match p, q with
  | Sum.inl a, Sum.inl b =>
      match D.eval f a b with
      | some c => Sum.inl c
      | none => patternTable D roots f p q
  | _, _ => patternTable D roots f p q

/-- One compatible total finite-complement observer for the whole pattern. -/
noncomputable def patternAlg
    (roots : List (RawAns Sigma D.Carrier)) :
    FiniteTagAlg D (patternSelected D roots).length where
  op := patternOp D roots
  preserve := by
    intro f a b c h
    change (match D.eval f a b with
      | some c' => Sum.inl c'
      | none => patternTable D roots f (Sum.inl a) (Sum.inl b)) = Sum.inl c
    rw [h]

/-- On every selected normalized suspension, the conservative pattern table
returns exactly its selected tag. -/
theorem patternOp_encode_susp
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (hs : RawAns.susp f l r ∈ patternSelected D roots)
    (hn : Normal D (RawAns.susp f l r)) :
    patternOp D roots f (patternEncode D roots l) (patternEncode D roots r) =
      patternEncode D roots (RawAns.susp f l r) := by
  classical
  have htable := patternTable_hit D hs
  cases l with
  | old a =>
      cases r with
      | old b =>
          have hnone : D.eval f a b = none := hn.2.2 a b rfl rfl
          simpa [patternOp, patternEncode, hnone] using htable
      | susp g r1 r2 =>
          have hrmem := (children_mem_patternSelected D hs).2
          simpa [patternOp, patternEncode, hrmem] using htable
  | susp g l1 l2 =>
      have hlmem := (children_mem_patternSelected D hs).1
      simpa [patternOp, patternEncode, hlmem] using htable

/-- The pattern observer evaluates every selected normalized node to its
injective encoding. -/
theorem foldRaw_eq_patternEncode
    {roots : List (RawAns Sigma D.Carrier)} :
    forall (s : RawAns Sigma D.Carrier),
      s ∈ patternSelected D roots -> Normal D s ->
        Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) s =
          patternEncode D roots s := by
  intro s
  induction s with
  | old a =>
      intro hs hn
      rfl
  | susp f l r ihl ihr =>
      intro hs hn
      have hc := children_mem_patternSelected D hs
      change patternOp D roots f
          (Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) l)
          (Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) r) =
        patternEncode D roots (RawAns.susp f l r)
      rw [ihl hc.1 hn.1, ihr hc.2 hn.2.1]
      exact patternOp_encode_susp D hs hn

/-- Generated Answers are normalized. -/
theorem generated_normal (x : Free.GeneratedAns D) : Normal D x.1 := by
  rcases x.2 with ⟨e, he⟩
  rw [← he]
  exact res_normal D e

/-- Raw roots underlying a finite list of generated Answers. -/
def rawRoots (xs : List (Free.GeneratedAns D)) :
    List (RawAns Sigma D.Carrier) := xs.map Subtype.val

/-- Membership of a generated Answer implies membership of its raw root. -/
theorem rawRoot_mem
    {xs : List (Free.GeneratedAns D)} {x : Free.GeneratedAns D}
    (hx : x ∈ xs) : x.1 ∈ rawRoots D xs := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
      simp only [List.mem_cons] at hx
      rcases hx with h | h
      · subst a
        simp [rawRoots]
      · have iht := ih h
        simp [rawRoots, iht]

/-- One finite-tag observer is simultaneously injective on any finite list of
generated Answers.  This is the finite-pattern strengthening of pairwise
separation. -/
theorem finitePatternRealization
    (xs : List (Free.GeneratedAns D)) :
    ∃ n : Nat, ∃ T : FiniteTagAlg D n,
      ∀ {x y : Free.GeneratedAns D}, x ∈ xs -> y ∈ xs ->
        Free.TotalAlg.interp D (T.toTotalAlg D) x =
          Free.TotalAlg.interp D (T.toTotalAlg D) y -> x = y := by
  classical
  let roots := rawRoots D xs
  refine ⟨(patternSelected D roots).length, patternAlg D roots, ?_⟩
  intro x y hx hy hxy
  have hxroot : x.1 ∈ roots := by
    exact rawRoot_mem D hx
  have hyroot : y.1 ∈ roots := by
    exact rawRoot_mem D hy
  have hxsel : x.1 ∈ patternSelected D roots :=
    root_mem_patternSelected D hxroot
  have hysel : y.1 ∈ patternSelected D roots :=
    root_mem_patternSelected D hyroot
  change Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) x.1 =
    Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) y.1 at hxy
  rw [foldRaw_eq_patternEncode D x.1 hxsel (generated_normal D x),
      foldRaw_eq_patternEncode D y.1 hysel (generated_normal D y)] at hxy
  have hraw : x.1 = y.1 :=
    patternEncode_injective_on D hxsel hysel hxy
  exact Subtype.ext hraw

/-- The old pairwise separation theorem is an immediate two-point consequence
of finite-pattern realization. -/
theorem pairSeparation_from_finitePattern
    (x y : Free.GeneratedAns D) (hxy : x ≠ y) :
    ∃ n : Nat, ∃ T : FiniteTagAlg D n,
      Free.TotalAlg.interp D (T.toTotalAlg D) x ≠
        Free.TotalAlg.interp D (T.toTotalAlg D) y := by
  rcases finitePatternRealization D [x, y] with ⟨n, T, hT⟩
  refine ⟨n, T, ?_⟩
  intro heq
  apply hxy
  exact hT (by simp) (by simp) heq

end FinitePatternRealization
end External
end Resolution
