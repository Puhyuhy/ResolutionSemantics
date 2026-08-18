import ResolutionFinitePatternRealization

/-!
# Point isolation from exact relative pattern recognition

Research branch probe.  The finite-pattern observer is stronger than the
published selected-node statement: on every normalized raw Answer it evaluates
to the global pattern encoding.  Consequently a singleton pattern observer
recognizes its chosen generated Answer among all generated Answers.
-/

universe u v

namespace Resolution
namespace External
namespace FinitePatternRealization

open FiniteTagProof

variable {Sigma : Signature.{u}}
variable (D : PartialAlg.{u,v} Sigma)

/-- An unselected suspension is encoded by the distinguished overflow state.
This is kept explicit rather than delegated to the simplifier because the
constructor separation is part of the structural argument below. -/
theorem patternEncode_susp_of_not_mem
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (h : RawAns.susp f l r ∉ patternSelected D roots) :
    patternEncode D roots (RawAns.susp f l r) = patternOverflow D := by
  classical
  unfold patternEncode
  rw [dif_neg h]

/-- If one side is selected, equality of pattern encodings already determines
the arbitrary other raw Answer.  The other Answer need not itself be selected.
The proof uses only explicit constructor disjointness of old/tag/overflow. -/
theorem eq_of_patternEncode_eq_of_mem_right
    {roots : List (RawAns Sigma D.Carrier)}
    {s t : RawAns Sigma D.Carrier}
    (ht : t ∈ patternSelected D roots)
    (henc : patternEncode D roots s = patternEncode D roots t) :
    s = t := by
  classical
  cases s with
  | old a =>
      cases t with
      | old b =>
          change
            (Sum.inl a : FiniteTagCarrier D (patternSelected D roots).length) =
              Sum.inl b at henc
          exact congrArg RawAns.old (Sum.inl.inj henc)
      | susp g l r =>
          rw [patternEncode_susp_of_mem D ht] at henc
          change
            (Sum.inl a : FiniteTagCarrier D (patternSelected D roots).length) =
              Sum.inr (Sum.inl
                (tagIndex (RawAns.susp g l r) (patternSelected D roots) ht)) at henc
          cases henc
  | susp f l r =>
      cases t with
      | old b =>
          by_cases hs : RawAns.susp f l r ∈ patternSelected D roots
          · rw [patternEncode_susp_of_mem D hs] at henc
            change
              (Sum.inr (Sum.inl
                (tagIndex (RawAns.susp f l r) (patternSelected D roots) hs)) :
                  FiniteTagCarrier D (patternSelected D roots).length) =
                Sum.inl b at henc
            cases henc
          · rw [patternEncode_susp_of_not_mem D hs] at henc
            change
              (Sum.inr (Sum.inr ()) :
                FiniteTagCarrier D (patternSelected D roots).length) =
                Sum.inl b at henc
            cases henc
      | susp g l' r' =>
          by_cases hs : RawAns.susp f l r ∈ patternSelected D roots
          · exact patternEncode_injective_on D hs ht henc
          · rw [patternEncode_susp_of_not_mem D hs,
              patternEncode_susp_of_mem D ht] at henc
            change
              (Sum.inr (Sum.inr ()) :
                FiniteTagCarrier D (patternSelected D roots).length) =
                Sum.inr (Sum.inl
                  (tagIndex (RawAns.susp g l' r')
                    (patternSelected D roots) ht)) at henc
            have hinner :
                (Sum.inr () :
                  Sum (Fin (patternSelected D roots).length) Unit) =
                  Sum.inl (tagIndex (RawAns.susp g l' r')
                    (patternSelected D roots) ht) :=
              Sum.inr.inj henc
            cases hinner

/-- An unselected suspension cannot accidentally hit the finite table through
children whose encodings coincide with selected children. -/
theorem patternTable_miss_of_not_mem
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (hs : RawAns.susp f l r ∉ patternSelected D roots) :
    patternTable D roots f (patternEncode D roots l) (patternEncode D roots r) =
      patternOverflow D := by
  classical
  have hnone : ¬(Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ patternSelected D roots ∧
        PatternMatchNode D roots f
          (patternEncode D roots l) (patternEncode D roots r) s) := by
    rintro ⟨s, hsmem, hm⟩
    cases s with
    | old a =>
        simp [PatternMatchNode] at hm
    | susp g l' r' =>
        have hm' : g = f ∧
            patternEncode D roots l' = patternEncode D roots l ∧
            patternEncode D roots r' = patternEncode D roots r := by
          simpa only [PatternMatchNode] using hm
        have hc := children_mem_patternSelected D hsmem
        have hl0 : l = l' :=
          eq_of_patternEncode_eq_of_mem_right D hc.1 hm'.2.1.symm
        have hr0 : r = r' :=
          eq_of_patternEncode_eq_of_mem_right D hc.2 hm'.2.2.symm
        have hl : l' = l := hl0.symm
        have hr : r' = r := hr0.symm
        cases hm'.1
        cases hl
        cases hr
        exact hs hsmem
  simp only [patternTable, dif_neg hnone]

/-- Every normalized unselected suspension evaluates to overflow after its
children have been encoded. -/
theorem patternOp_encode_susp_of_not_mem
    {roots : List (RawAns Sigma D.Carrier)}
    {f : Sigma.Op} {l r : RawAns Sigma D.Carrier}
    (hs : RawAns.susp f l r ∉ patternSelected D roots)
    (hn : Normal D (RawAns.susp f l r)) :
    patternOp D roots f (patternEncode D roots l) (patternEncode D roots r) =
      patternOverflow D := by
  classical
  have htable := patternTable_miss_of_not_mem D hs
  cases l with
  | old a =>
      cases r with
      | old b =>
          have hnone : D.eval f a b = none := hn.2.2 a b rfl rfl
          simpa [patternOp, patternEncode, hnone] using htable
      | susp g r1 r2 =>
          by_cases hrmem : RawAns.susp g r1 r2 ∈ patternSelected D roots
          · rw [patternEncode_susp_of_mem D hrmem] at htable ⊢
            simpa [patternOp] using htable
          · have hrenc := patternEncode_susp_of_not_mem D hrmem
            rw [hrenc] at htable ⊢
            simpa [patternOp, patternOverflow] using htable
  | susp g l1 l2 =>
      by_cases hlmem : RawAns.susp g l1 l2 ∈ patternSelected D roots
      · rw [patternEncode_susp_of_mem D hlmem] at htable ⊢
        simpa [patternOp] using htable
      · have hlenc := patternEncode_susp_of_not_mem D hlmem
        rw [hlenc] at htable ⊢
        simpa [patternOp, patternOverflow] using htable

/-- Exact global recognition: the finite-pattern observer computes the declared
pattern encoding on every normalized raw Answer, not only on selected nodes. -/
theorem foldRaw_eq_patternEncode_all
    {roots : List (RawAns Sigma D.Carrier)} :
    forall (s : RawAns Sigma D.Carrier),
      Normal D s ->
        Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) s =
          patternEncode D roots s := by
  intro s
  induction s with
  | old a =>
      intro hn
      rfl
  | susp f l r ihl ihr =>
      intro hn
      change patternOp D roots f
          (Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) l)
          (Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) r) =
        patternEncode D roots (RawAns.susp f l r)
      rw [ihl hn.1, ihr hn.2.1]
      by_cases hs : RawAns.susp f l r ∈ patternSelected D roots
      · exact patternOp_encode_susp D hs hn
      · have hop := patternOp_encode_susp_of_not_mem D hs hn
        rw [patternEncode_susp_of_not_mem D hs]
        exact hop

/-- A singleton pattern observer recognizes its chosen generated Answer among
all generated Answers. -/
theorem singletonPatternObserver_recognizes
    (x y : Free.GeneratedAns D) :
    Free.TotalAlg.interp D ((patternAlg D [x.1]).toTotalAlg D) y =
        Free.TotalAlg.interp D ((patternAlg D [x.1]).toTotalAlg D) x ->
      y = x := by
  intro h
  change Free.TotalAlg.foldRaw D ((patternAlg D [x.1]).toTotalAlg D) y.1 =
    Free.TotalAlg.foldRaw D ((patternAlg D [x.1]).toTotalAlg D) x.1 at h
  rw [foldRaw_eq_patternEncode_all D y.1 (generated_normal D y),
      foldRaw_eq_patternEncode_all D x.1 (generated_normal D x)] at h
  have hxsel : x.1 ∈ patternSelected D [x.1] :=
    root_mem_patternSelected D (by simp)
  have hraw : y.1 = x.1 :=
    eq_of_patternEncode_eq_of_mem_right D hxsel h
  exact Subtype.ext hraw

/-- Publication-independent point-isolation form: every generated Answer has a
finite-tag observer whose fiber at that Answer is a singleton. -/
theorem generatedPointIsolated
    (x : Free.GeneratedAns D) :
    ∃ n : Nat, ∃ T : FiniteTagAlg D n,
      ∀ y : Free.GeneratedAns D,
        Free.TotalAlg.interp D (T.toTotalAlg D) y =
          Free.TotalAlg.interp D (T.toTotalAlg D) x ↔ y = x := by
  let n := (patternSelected D [x.1]).length
  let T : FiniteTagAlg D n := patternAlg D [x.1]
  refine ⟨n, T, ?_⟩
  intro y
  constructor
  · exact singletonPatternObserver_recognizes D x y
  · intro hy
    cases hy
    rfl

end FinitePatternRealization
end External
end Resolution
