import ResolutionFinitePatternRealization
import ResolutionOrbitCompressionMaster

/-!
# Finite-pattern escape as the Resolution-specific anti-limit mechanism

Orbit compression explains why factorial sampling is Cauchy. It does not, by
itself, explain why the resulting Cauchy sequence has no generated limit.

This module isolates that second ingredient. For a generated unary syntactic
orbit

    t_(k+1) = susp stepOp t_k (old fixedRight),

syntax grows strictly at every step. Given any candidate generated Answer x,
we select the finite subterm pattern consisting of x and a sufficiently long
orbit prefix. The finite-pattern observer realizes that whole finite pattern,
but the very next orbit node is too large to belong to it. Therefore the next
transition misses the finite table and enters overflow. Since no selected node
can have overflow as an encoded child, overflow is absorbing along the unary
context. All sufficiently late orbit terms are thus separated from x by one
candidate-tailored finite-complement observer.

Combined with trajectory compression, this yields a reusable proper-completion
theorem. The finite-base comb and old-fixing infinite-base constructions are
both instances.
-/

universe u v

namespace Resolution
namespace FinitePatternAntiLimit

open Resolution.External
open Resolution.Orbit
open Resolution.External.FiniteTagProof
open Resolution.External.FinitePatternRealization
open Resolution.OrbitCompression

variable {Sigma : Signature.{u}}

structure EscapingUnarySyntax
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D) where
  stepOp : Sigma.Op
  fixedRight : D.Carrier
  raw_succ : forall k : Nat,
    (W.term (k + 1)).1 =
      RawAns.susp stepOp (W.term k).1 (.old fixedRight)

namespace EscapingUnarySyntax

variable {D : PartialAlg.{u,v} Sigma}
variable {W : ObserverOrbitCompression D}

theorem nodeCount_succ
    (U : EscapingUnarySyntax W) (k : Nat) :
    nodeCount D (W.term (k + 1)).1 = nodeCount D (W.term k).1 + 2 := by
  rw [U.raw_succ k]
  simp only [nodeCount]
  omega

theorem index_le_nodeCount
    (U : EscapingUnarySyntax W) : forall k : Nat,
      k <= nodeCount D (W.term k).1
  | 0 => Nat.zero_le _
  | k + 1 => by
      rw [nodeCount_succ U k]
      have hk := index_le_nodeCount U k
      omega

end EscapingUnarySyntax

def escapePrefixIndex
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D) (x : Free.GeneratedAns D) : Nat :=
  nodeCount D x.1 + 1

def escapeRoots
    {D : PartialAlg.{u,v} Sigma}
    (W : ObserverOrbitCompression D) (x : Free.GeneratedAns D) :
    List (RawAns Sigma D.Carrier) :=
  [x.1, (W.term (escapePrefixIndex W x)).1]

theorem patternEncode_ne_overflow_of_mem
    (D : PartialAlg.{u,v} Sigma)
    {roots : List (RawAns Sigma D.Carrier)}
    {s : RawAns Sigma D.Carrier}
    (hs : s ∈ patternSelected D roots) :
    patternEncode D roots s ≠ patternOverflow D := by
  classical
  cases s with
  | old a =>
      simp [patternEncode, patternOverflow]
  | susp f l r =>
      rw [patternEncode_susp_of_mem D hs]
      simp [patternOverflow]

theorem patternTable_overflow_left
    (D : PartialAlg.{u,v} Sigma)
    (roots : List (RawAns Sigma D.Carrier))
    (g : Sigma.Op)
    (q : FiniteTagCarrier D (patternSelected D roots).length) :
    patternTable D roots g (patternOverflow D) q = patternOverflow D := by
  classical
  have hnone : ¬(Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ patternSelected D roots ∧
        PatternMatchNode D roots g (patternOverflow D) q s) := by
    rintro ⟨s, hs, hm⟩
    cases s with
    | old a =>
        simp [PatternMatchNode] at hm
    | susp f l r =>
        have hlmem := (children_mem_patternSelected D hs).1
        have hne := patternEncode_ne_overflow_of_mem D hlmem
        have hm0 := hm
        simp only [PatternMatchNode] at hm0
        exact hne hm0.2.1
  simp only [patternTable, dif_neg hnone]

theorem patternOp_overflow_left
    (D : PartialAlg.{u,v} Sigma)
    (roots : List (RawAns Sigma D.Carrier))
    (g : Sigma.Op)
    (q : FiniteTagCarrier D (patternSelected D roots).length) :
    patternOp D roots g (patternOverflow D) q = patternOverflow D := by
  change patternTable D roots g (patternOverflow D) q = patternOverflow D
  exact patternTable_overflow_left D roots g q

section OrbitEscape

variable (D : PartialAlg.{u,v} Sigma)
variable (W : ObserverOrbitCompression D)

theorem candidate_mem_escapeSelected (x : Free.GeneratedAns D) :
    x.1 ∈ patternSelected D (escapeRoots W x) := by
  apply root_mem_patternSelected D
  simp [escapeRoots]

theorem prefix_mem_escapeSelected (x : Free.GeneratedAns D) :
    (W.term (escapePrefixIndex W x)).1 ∈
      patternSelected D (escapeRoots W x) := by
  apply root_mem_patternSelected D
  simp [escapeRoots]

theorem fixedRight_mem_escapeSelected
    (U : EscapingUnarySyntax W) (x : Free.GeneratedAns D) :
    (.old U.fixedRight : RawAns Sigma D.Carrier) ∈
      patternSelected D (escapeRoots W x) := by
  let n := nodeCount D x.1
  have hp := prefix_mem_escapeSelected D W x
  change (W.term (n + 1)).1 ∈ patternSelected D (escapeRoots W x) at hp
  have hshape := U.raw_succ n
  rw [hshape] at hp
  exact (children_mem_patternSelected D hp).2

theorem next_not_escapeSelected
    (U : EscapingUnarySyntax W) (x : Free.GeneratedAns D) :
    (W.term (nodeCount D x.1 + 2)).1 ∉
      patternSelected D (escapeRoots W x) := by
  intro hmem
  simp only [escapeRoots, escapePrefixIndex, patternSelected,
    List.mem_append, List.mem_nil_iff, or_false] at hmem
  rcases hmem with hx | hp
  · have hle := Resolution.FiniteBaseProperness.nodeCount_le_of_mem_subterms D hx
    have hindex := EscapingUnarySyntax.index_le_nodeCount U
      (nodeCount D x.1 + 2)
    omega
  · have hle := Resolution.FiniteBaseProperness.nodeCount_le_of_mem_subterms D hp
    have hsucc := EscapingUnarySyntax.nodeCount_succ U
      (nodeCount D x.1 + 1)
    have hidx : nodeCount D x.1 + 1 + 1 = nodeCount D x.1 + 2 := by omega
    rw [hidx] at hsucc
    omega

theorem patternTable_after_escapePrefix
    (U : EscapingUnarySyntax W) (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    let p := (W.term (escapePrefixIndex W x)).1
    patternTable D roots U.stepOp
        (patternEncode D roots p)
        (patternEncode D roots (.old U.fixedRight)) =
      patternOverflow D := by
  classical
  let roots := escapeRoots W x
  let p := (W.term (escapePrefixIndex W x)).1
  have hpRoot : p ∈ patternSelected D roots := by
    exact prefix_mem_escapeSelected D W x
  have hzSel : (.old U.fixedRight : RawAns Sigma D.Carrier) ∈
      patternSelected D roots := by
    exact fixedRight_mem_escapeSelected D W U x
  have hnext : (W.term (nodeCount D x.1 + 2)).1 ∉
      patternSelected D roots := by
    exact next_not_escapeSelected D W U x
  have hnone : ¬(Exists fun s : RawAns Sigma D.Carrier =>
      s ∈ patternSelected D roots ∧
        PatternMatchNode D roots U.stepOp
          (patternEncode D roots p)
          (patternEncode D roots (.old U.fixedRight)) s) := by
    rintro ⟨s, hs, hm⟩
    cases s with
    | old a =>
        simp [PatternMatchNode] at hm
    | susp g l r =>
        have hc := children_mem_patternSelected D hs
        have hm0 := hm
        simp only [PatternMatchNode] at hm0
        have hl : l = p :=
          patternEncode_injective_on D hc.1 hpRoot hm0.2.1
        have hr : r = .old U.fixedRight :=
          patternEncode_injective_on D hc.2 hzSel hm0.2.2
        have hsNext : RawAns.susp g l r =
            (W.term (nodeCount D x.1 + 2)).1 := by
          rw [U.raw_succ (nodeCount D x.1 + 1)]
          cases hm0.1
          cases hl
          cases hr
          rfl
        exact hnext (hsNext ▸ hs)
  change patternTable D roots U.stepOp
      (patternEncode D roots p)
      (patternEncode D roots (.old U.fixedRight)) = patternOverflow D
  simp only [patternTable, dif_neg hnone]

theorem patternOp_after_escapePrefix
    (U : EscapingUnarySyntax W) (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    let p := (W.term (escapePrefixIndex W x)).1
    patternOp D roots U.stepOp
        (patternEncode D roots p)
        (patternEncode D roots (.old U.fixedRight)) =
      patternOverflow D := by
  let roots := escapeRoots W x
  let p := (W.term (escapePrefixIndex W x)).1
  change patternOp D roots U.stepOp
      (patternEncode D roots p)
      (patternEncode D roots (.old U.fixedRight)) = patternOverflow D
  have hpRoot : p ∈ patternSelected D roots :=
    prefix_mem_escapeSelected D W x
  let n := nodeCount D x.1
  have hpShape : p =
      RawAns.susp U.stepOp (W.term n).1 (.old U.fixedRight) := by
    change (W.term (n + 1)).1 =
      RawAns.susp U.stepOp (W.term n).1 (.old U.fixedRight)
    exact U.raw_succ n
  have hsusp : RawAns.susp U.stepOp (W.term n).1 (.old U.fixedRight) ∈
      patternSelected D roots := by
    rw [← hpShape]
    exact hpRoot
  have hpenc := patternEncode_susp_of_mem D hsusp
  have htable := patternTable_after_escapePrefix D W U x
  change patternTable D roots U.stepOp
      (patternEncode D roots p)
      (patternEncode D roots (.old U.fixedRight)) = patternOverflow D at htable
  have hpenc' : patternEncode D roots p =
      (Sum.inr (Sum.inl
        (tagIndex
          (RawAns.susp U.stepOp (W.term n).1 (.old U.fixedRight))
          (patternSelected D roots) hsusp)) :
        FiniteTagCarrier D (patternSelected D roots).length) := by
    rw [hpShape]
    exact hpenc
  rw [hpenc']
  change patternTable D roots U.stepOp
      (Sum.inr (Sum.inl
        (tagIndex
          (RawAns.susp U.stepOp (W.term n).1 (.old U.fixedRight))
          (patternSelected D roots) hsusp)))
      (patternEncode D roots (.old U.fixedRight)) = patternOverflow D
  rw [hpenc'] at htable
  exact htable

theorem fold_escapePrefix_eq_encode (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    let p := (W.term (escapePrefixIndex W x)).1
    Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) p =
      patternEncode D roots p := by
  let roots := escapeRoots W x
  let p := (W.term (escapePrefixIndex W x)).1
  have hp : p ∈ patternSelected D roots :=
    prefix_mem_escapeSelected D W x
  have hn : Normal D p := generated_normal D (W.term (escapePrefixIndex W x))
  exact foldRaw_eq_patternEncode D p hp hn

theorem fold_candidate_eq_encode (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) x.1 =
      patternEncode D roots x.1 := by
  let roots := escapeRoots W x
  have hx : x.1 ∈ patternSelected D roots :=
    candidate_mem_escapeSelected D W x
  exact foldRaw_eq_patternEncode D x.1 hx (generated_normal D x)

theorem fold_escapeNext_eq_overflow
    (U : EscapingUnarySyntax W) (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D)
        (W.term (nodeCount D x.1 + 2)).1 = patternOverflow D := by
  dsimp only
  rw [U.raw_succ (nodeCount D x.1 + 1)]
  change patternOp D (escapeRoots W x) U.stepOp
      (Free.TotalAlg.foldRaw D ((patternAlg D (escapeRoots W x)).toTotalAlg D)
        (W.term (nodeCount D x.1 + 1)).1)
      (Sum.inl U.fixedRight) = patternOverflow D
  have hp := fold_escapePrefix_eq_encode D W x
  change Free.TotalAlg.foldRaw D
      ((patternAlg D (escapeRoots W x)).toTotalAlg D)
      (W.term (nodeCount D x.1 + 1)).1 =
    patternEncode D (escapeRoots W x)
      (W.term (nodeCount D x.1 + 1)).1 at hp
  rw [hp]
  have hop := patternOp_after_escapePrefix D W U x
  change patternOp D (escapeRoots W x) U.stepOp
      (patternEncode D (escapeRoots W x)
        (W.term (nodeCount D x.1 + 1)).1)
      (Sum.inl U.fixedRight) = patternOverflow D at hop
  exact hop

theorem fold_escapeTail_eq_overflow
    (U : EscapingUnarySyntax W) (x : Free.GeneratedAns D) :
    let roots := escapeRoots W x
    forall d : Nat,
      Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D)
          (W.term (nodeCount D x.1 + 2 + d)).1 = patternOverflow D := by
  dsimp only
  intro d
  induction d with
  | zero =>
      simpa using fold_escapeNext_eq_overflow D W U x
  | succ d ih =>
      have hindex : nodeCount D x.1 + 2 + (d + 1) =
          (nodeCount D x.1 + 2 + d) + 1 := by omega
      rw [hindex, U.raw_succ (nodeCount D x.1 + 2 + d)]
      change patternOp D (escapeRoots W x) U.stepOp
          (Free.TotalAlg.foldRaw D
            ((patternAlg D (escapeRoots W x)).toTotalAlg D)
            (W.term (nodeCount D x.1 + 2 + d)).1)
          (Sum.inl U.fixedRight) = patternOverflow D
      rw [ih]
      exact patternOp_overflow_left D (escapeRoots W x)
        U.stepOp (Sum.inl U.fixedRight)

theorem noGeneratedLimit_of_escapingSyntax
    (U : EscapingUnarySyntax W) : NoGeneratedLimit W := by
  intro x hconv
  let roots := escapeRoots W x
  let stage := (patternSelected D roots).length
  rcases hconv stage with ⟨N, hN⟩
  let K := N + nodeCount D x.1 + 2
  have hNK : N <= K := by omega
  have hlarge : nodeCount D x.1 + 2 <= fact K := by
    have hKfact := le_fact K
    omega
  have hindex : nodeCount D x.1 + 2 +
      (fact K - (nodeCount D x.1 + 2)) = fact K := by omega
  have hxMem : x.1 ∈ patternSelected D roots :=
    candidate_mem_escapeSelected D W x
  have hxFold :
      Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) x.1 =
        patternEncode D roots x.1 :=
    fold_candidate_eq_encode D W x
  have htail :
      Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D)
          (W.term (fact K)).1 = patternOverflow D := by
    rw [← hindex]
    exact fold_escapeTail_eq_overflow D W U x
      (fact K - (nodeCount D x.1 + 2))
  have hmodel := hN K hNK (patternAlg D roots)
  change Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D) x.1 =
    Free.TotalAlg.foldRaw D ((patternAlg D roots).toTotalAlg D)
      (W.term (fact K)).1 at hmodel
  rw [hxFold, htail] at hmodel
  exact (patternEncode_ne_overflow_of_mem D hxMem) hmodel

theorem notComplete_of_compressed_escapingSyntax
    (W : ObserverOrbitCompression D)
    (U : EscapingUnarySyntax W) :
    ¬ Filtered.Complete (generatedFilteredSpace D) :=
  notComplete_of_compression W (noGeneratedLimit_of_escapingSyntax D W U)

theorem embeddingNotSurjective_of_compressed_escapingSyntax
    (W : ObserverOrbitCompression D)
    (U : EscapingUnarySyntax W) :
    ¬ Function.Surjective (Filtered.embed (generatedFilteredSpace D)) :=
  embeddingNotSurjective_of_compression W
    (noGeneratedLimit_of_escapingSyntax D W U)

end OrbitEscape

noncomputable def finiteBaseEscapingSyntax
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a z : D.Carrier)
    {baseSize : Nat}
    (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    EscapingUnarySyntax
      (finiteBaseCompression D f a z C hUndefined) where
  stepOp := f
  fixedRight := z
  raw_succ := by
    intro k
    change Resolution.Probe.combRaw D f a z (k + 1) =
      RawAns.susp f (Resolution.Probe.combRaw D f a z k) (.old z)
    exact Resolution.Probe.combRaw_succ D f a z hUndefined k

noncomputable def oldFixingEscapingSyntax
    (D : PartialAlg.{u,v} Sigma)
    (W : OldFixingContextWitness D) :
    EscapingUnarySyntax (oldFixingCompression D W) where
  stepOp := W.stepOp
  fixedRight := W.fixedRight
  raw_succ := by
    intro k
    rfl

theorem finiteBase_noGeneratedLimit_via_finitePattern
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a z : D.Carrier)
    {baseSize : Nat}
    (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    NoGeneratedLimit (finiteBaseCompression D f a z C hUndefined) :=
  noGeneratedLimit_of_escapingSyntax D
    (finiteBaseCompression D f a z C hUndefined)
    (finiteBaseEscapingSyntax D f a z C hUndefined)

theorem oldFixing_noGeneratedLimit_via_finitePattern
    (D : PartialAlg.{u,v} Sigma)
    (W : OldFixingContextWitness D) :
    NoGeneratedLimit (oldFixingCompression D W) :=
  noGeneratedLimit_of_escapingSyntax D
    (oldFixingCompression D W) (oldFixingEscapingSyntax D W)

theorem finiteBase_notComplete_via_master
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op) (a z : D.Carrier)
    {baseSize : Nat}
    (C : Coded D.Carrier baseSize)
    (hUndefined : D.eval f a z = none) :
    ¬ Filtered.Complete (generatedFilteredSpace D) :=
  notComplete_of_compressed_escapingSyntax D
    (finiteBaseCompression D f a z C hUndefined)
    (finiteBaseEscapingSyntax D f a z C hUndefined)

theorem oldFixing_notComplete_via_master
    (D : PartialAlg.{u,v} Sigma)
    (W : OldFixingContextWitness D) :
    ¬ Filtered.Complete (generatedFilteredSpace D) :=
  notComplete_of_compressed_escapingSyntax D
    (oldFixingCompression D W) (oldFixingEscapingSyntax D W)

end FinitePatternAntiLimit
end Resolution
