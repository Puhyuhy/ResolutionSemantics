import ResolutionRelativeSeparation

/-!
# Intrinsic finite-complement separation

The primitive condition in this module does not contain an equivalence to the
canonical finite-tag carrier.  It requires only that the complement of the
pointwise-preserved old image inject into a finite type.

A budget `n` means that the whole non-base complement has at most `n + 1`
elements.  This convention matches the existing implementation, which uses
`n` fresh tags and one overflow state.  The main theorem proves that this
intrinsic separation predicate is equivalent, at the same budget, to the
concrete finite-tag predicate.
-/

universe u v w

namespace Resolution
namespace External

variable {Sigma : Signature.{u}}

/-- Elements of a compatible total extension outside the embedded old carrier. -/
abbrev OldComplement
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.TotalAlg.{u,v,w} D) :=
  {z : T.Carrier // forall a : D.Carrier, z ≠ T.embed a}

/-- Publication-facing name for the part of a compatible extension outside
    the pointwise-preserved old carrier. -/
abbrev OutsideOld
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.TotalAlg.{u,v,w} D) :=
  OldComplement D T

/-- Every compatible extension decomposes, as a carrier, into its embedded old
    points and the genuine outside points.  This is independent of any finite
    budget or chosen finite-tag presentation. -/
noncomputable def oldOrOutsideEquiv
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.TotalAlg.{u,v,w} D) :
    CarrierBijection T.Carrier (D.Carrier ⊕ OutsideOld D T) := by
  classical
  refine {
    toFun := fun z =>
      if h : Exists fun a : D.Carrier => T.embed a = z then
        Sum.inl (Classical.choose h)
      else
        Sum.inr ⟨z, by
          intro a hza
          exact h ⟨a, hza.symm⟩⟩
    invFun := fun q =>
      match q with
      | Sum.inl a => T.embed a
      | Sum.inr z => z.1
    left_inv := ?_
    right_inv := ?_
  }
  · intro z
    by_cases h : Exists fun a : D.Carrier => T.embed a = z
    · simp only [dif_pos h]
      exact Classical.choose_spec h
    · simp only [dif_neg h]
  · intro q
    cases q with
    | inl a =>
        have h : Exists fun b : D.Carrier => T.embed b = T.embed a :=
          ⟨a, rfl⟩
        simp only [dif_pos h]
        apply congrArg Sum.inl
        apply T.embed_injective
        exact Classical.choose_spec h
    | inr z =>
        have h : Not (Exists fun a : D.Carrier => T.embed a = z.1) := by
          rintro ⟨a, ha⟩
          exact z.2 a ha.symm
        simp only [dif_neg h]

/-- Intrinsic budget condition: the non-base complement injects into
    `Fin (n + 1)`.  No sum presentation or distinguished overflow element is
    part of this definition. -/
def ComplementBudget
    (D : PartialAlg.{u,v} Sigma)
    (T : Free.TotalAlg.{u,v,w} D)
    (n : Nat) : Prop :=
  Exists fun code : OldComplement D T -> Fin (n + 1) =>
    Function.Injective code

/-- A compatible total extension with intrinsically bounded finite complement. -/
structure IntrinsicFiniteComplementExtension
    (D : PartialAlg.{u,v} Sigma) (n : Nat) where
  toTotalAlg : Free.TotalAlg.{u,v,w} D
  complement_budget : ComplementBudget D toTotalAlg n

namespace IntrinsicFiniteComplementExtension

variable {D : PartialAlg.{u,v} Sigma} {n : Nat}

noncomputable def complementCode
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    OldComplement D E.toTotalAlg -> Fin (n + 1) :=
  Classical.choose E.complement_budget

theorem complementCode_injective
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    Function.Injective E.complementCode :=
  Classical.choose_spec E.complement_budget

/-- Convert a code in `Fin (n+1)` to `n` ordinary tags plus one reserve state. -/
def finSuccToTag (n : Nat) (i : Fin (n + 1)) : Fin n ⊕ Unit :=
  if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr ()

/-- Convert `n` tags plus one reserve state back to `Fin (n+1)`. -/
def tagToFinSucc (n : Nat) : Fin n ⊕ Unit -> Fin (n + 1)
  | Sum.inl i => ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩
  | Sum.inr _ => ⟨n, Nat.lt_succ_self n⟩

@[simp] theorem tagToFinSucc_finSuccToTag
    (n : Nat) (i : Fin (n + 1)) :
    tagToFinSucc n (finSuccToTag n i) = i := by
  unfold finSuccToTag
  split
  next h =>
    simp only [tagToFinSucc]
  next h =>
    simp only [tagToFinSucc]
    apply Fin.ext
    exact Nat.le_antisymm
      (Nat.le_of_not_gt h)
      (Nat.le_of_lt_succ i.isLt)

@[simp] theorem finSuccToTag_tagToFinSucc
    (n : Nat) (q : Fin n ⊕ Unit) :
    finSuccToTag n (tagToFinSucc n q) = q := by
  cases q with
  | inl i =>
      simp only [tagToFinSucc]
      unfold finSuccToTag
      rw [dif_pos i.isLt]
  | inr u =>
      cases u
      simp only [tagToFinSucc]
      unfold finSuccToTag
      rw [dif_neg (Nat.lt_irrefl n)]

theorem tagToFinSucc_injective
    (n : Nat) : Function.Injective (tagToFinSucc n) := by
  intro x y hxy
  calc
    x = finSuccToTag n (tagToFinSucc n x) :=
      (finSuccToTag_tagToFinSucc n x).symm
    _ = finSuccToTag n (tagToFinSucc n y) :=
      congrArg (finSuccToTag n) hxy
    _ = y := finSuccToTag_tagToFinSucc n y

def asComplement
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (z : E.toTotalAlg.Carrier)
    (h : Not (Exists fun a : D.Carrier => E.toTotalAlg.embed a = z)) :
    OldComplement D E.toTotalAlg :=
  ⟨z, by
    intro a hza
    exact h ⟨a, hza.symm⟩⟩

/-- Encode an arbitrary target element in the canonical finite-tag carrier. -/
noncomputable def encode
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (z : E.toTotalAlg.Carrier) : FiniteTagCarrier D n := by
  classical
  exact if h : Exists fun a : D.Carrier => E.toTotalAlg.embed a = z then
    Sum.inl (Classical.choose h)
  else
    Sum.inr (finSuccToTag n
      (E.complementCode (E.asComplement z h)))

noncomputable def decodeComplement
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (i : Fin (n + 1)) : Option E.toTotalAlg.Carrier := by
  classical
  exact if h : Exists fun c : OldComplement D E.toTotalAlg =>
      E.complementCode c = i then
    some (Classical.choose h).1
  else
    none

noncomputable def decode
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    FiniteTagCarrier D n -> Option E.toTotalAlg.Carrier
  | Sum.inl a => some (E.toTotalAlg.embed a)
  | Sum.inr q => E.decodeComplement (tagToFinSucc n q)

@[simp] theorem encode_embed
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (a : D.Carrier) :
    E.encode (E.toTotalAlg.embed a) =
      (Sum.inl a : FiniteTagCarrier D n) := by
  classical
  unfold encode
  have h : Exists fun b : D.Carrier =>
      E.toTotalAlg.embed b = E.toTotalAlg.embed a := ⟨a, rfl⟩
  rw [dif_pos h]
  apply congrArg Sum.inl
  apply E.toTotalAlg.embed_injective
  exact Classical.choose_spec h

@[simp] theorem decodeComplement_code
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (c : OldComplement D E.toTotalAlg) :
    E.decodeComplement (E.complementCode c) = some c.1 := by
  classical
  unfold decodeComplement
  have h : Exists fun d : OldComplement D E.toTotalAlg =>
      E.complementCode d = E.complementCode c := ⟨c, rfl⟩
  rw [dif_pos h]
  have hdc : Classical.choose h = c :=
    E.complementCode_injective (Classical.choose_spec h)
  rw [hdc]

@[simp] theorem decode_encode
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (z : E.toTotalAlg.Carrier) :
    E.decode (E.encode z) = some z := by
  classical
  by_cases hOld : Exists fun a : D.Carrier =>
      E.toTotalAlg.embed a = z
  · rcases hOld with ⟨a, ha⟩
    subst z
    rw [encode_embed]
    rfl
  · let c := E.asComplement z hOld
    have hEncode : E.encode z =
        Sum.inr (finSuccToTag n (E.complementCode c)) := by
      unfold encode
      rw [dif_neg hOld]
    rw [hEncode]
    change E.decodeComplement
      (tagToFinSucc n (finSuccToTag n (E.complementCode c))) = some z
    rw [tagToFinSucc_finSuccToTag, decodeComplement_code]
    rfl

theorem encode_injective
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    Function.Injective E.encode := by
  intro x y hxy
  have h := congrArg E.decode hxy
  simpa using h

/-- An intrinsic finite-complement extension has a derived base-fixing
    injection into the canonical finite-tag carrier.  This deliberately does
    not assert a bijection: the intrinsic budget is an upper bound, so some
    canonical tag states may be unused. -/
theorem intrinsicExtensionHasCanonicalPresentation
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    Exists fun code : E.toTotalAlg.Carrier -> FiniteTagCarrier D n =>
      Function.Injective code ∧
      forall a : D.Carrier,
        code (E.toTotalAlg.embed a) =
          (Sum.inl a : FiniteTagCarrier D n) :=
  ⟨E.encode, E.encode_injective, E.encode_embed⟩

/-- Transport the intrinsic extension to the canonical finite-tag carrier.
    Unused finite-tag states decode to `none` and are sent to overflow. -/
noncomputable def toFiniteTagAlg
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    FiniteTagAlg D n where
  op := fun f p q =>
    match E.decode p, E.decode q with
    | some x, some y => E.encode (E.toTotalAlg.op f x y)
    | _, _ => Sum.inr (Sum.inr ())
  preserve := by
    intro f a b c h
    change E.encode
      (E.toTotalAlg.op f (E.toTotalAlg.embed a) (E.toTotalAlg.embed b)) =
        (Sum.inl c : FiniteTagCarrier D n)
    rw [E.toTotalAlg.preserve f a b c h]
    exact E.encode_embed c

theorem foldRaw_toFiniteTagAlg
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    forall t : RawAns Sigma D.Carrier,
      Free.TotalAlg.foldRaw D ((E.toFiniteTagAlg).toTotalAlg D) t =
        E.encode (Free.TotalAlg.foldRaw D E.toTotalAlg t)
  | .old a => (E.encode_embed a).symm
  | .susp f x y => by
      simp only [Free.TotalAlg.foldRaw]
      rw [foldRaw_toFiniteTagAlg E x, foldRaw_toFiniteTagAlg E y]
      change (match E.decode
          (E.encode (Free.TotalAlg.foldRaw D E.toTotalAlg x)),
        E.decode (E.encode (Free.TotalAlg.foldRaw D E.toTotalAlg y)) with
        | some l, some r => E.encode (E.toTotalAlg.op f l r)
        | _, _ => Sum.inr (Sum.inr ())) = _
      rw [E.decode_encode, E.decode_encode]

theorem interp_toFiniteTagAlg
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n)
    (x : Free.GeneratedAns D) :
    Free.TotalAlg.interp D ((E.toFiniteTagAlg).toTotalAlg D) x =
      E.encode (Free.TotalAlg.interp D E.toTotalAlg x) :=
  E.foldRaw_toFiniteTagAlg x.1

end IntrinsicFiniteComplementExtension

/-- Short namespace-level facade for the derived base-fixing canonical
    encoding. -/
theorem intrinsicExtensionHasCanonicalPresentation
    {D : PartialAlg.{u,v} Sigma} {n : Nat}
    (E : IntrinsicFiniteComplementExtension.{u,v,w} D n) :
    Exists fun code : E.toTotalAlg.Carrier -> FiniteTagCarrier D n =>
      Function.Injective code ∧
      forall a : D.Carrier,
        code (E.toTotalAlg.embed a) =
          (Sum.inl a : FiniteTagCarrier D n) :=
  E.intrinsicExtensionHasCanonicalPresentation

/-- The outside part of a canonical finite-tag model is exactly its `n` tags
    plus the reserve/overflow state. -/
def outsideEquiv
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (T : FiniteTagAlg D n) :
    CarrierBijection
      (OutsideOld D (T.toTotalAlg D))
      (Fin n ⊕ Unit) where
  toFun
    | ⟨Sum.inl a, h⟩ => False.elim (h a rfl)
    | ⟨Sum.inr q, _⟩ => q
  invFun q :=
    ⟨Sum.inr q, by
      intro a h
      cases h⟩
  left_inv
    | ⟨Sum.inl a, h⟩ => False.elim (h a rfl)
    | ⟨Sum.inr q, _⟩ => rfl
  right_inv q := rfl

/-- Code the intrinsic complement of a concrete finite-tag algebra. -/
def finiteTagComplementCode
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (T : FiniteTagAlg D n) :
    OldComplement D (T.toTotalAlg D) -> Fin (n + 1)
  | ⟨Sum.inl a, h⟩ => False.elim (h a rfl)
  | ⟨Sum.inr q, _⟩ =>
      IntrinsicFiniteComplementExtension.tagToFinSucc n q

theorem finiteTagComplementCode_injective
    (D : PartialAlg.{u,v} Sigma) (n : Nat)
    (T : FiniteTagAlg D n) :
    Function.Injective (finiteTagComplementCode D n T) := by
  intro x y hxy
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  cases x with
  | inl a => exact False.elim (hx a rfl)
  | inr qx =>
      cases y with
      | inl b => exact False.elim (hy b rfl)
      | inr qy =>
          apply Subtype.ext
          apply congrArg Sum.inr
          exact IntrinsicFiniteComplementExtension.tagToFinSucc_injective n hxy

/-- Every concrete finite-tag algebra is an intrinsic finite-complement
    extension at the same budget. -/
def intrinsicOfFiniteTagAlg
    (D : PartialAlg.{u,v} Sigma) {n : Nat}
    (T : FiniteTagAlg D n) :
    IntrinsicFiniteComplementExtension.{u,v,v} D n where
  toTotalAlg := T.toTotalAlg D
  complement_budget :=
    ⟨finiteTagComplementCode D n T,
      finiteTagComplementCode_injective D n T⟩

def IntrinsicFiniteComplementSeparatesAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (n : Nat) : Prop :=
  Exists fun E : IntrinsicFiniteComplementExtension.{u,v,v} D n =>
    Free.TotalAlg.interp D E.toTotalAlg x ≠
      Free.TotalAlg.interp D E.toTotalAlg y

/-- The intrinsic and canonical separation predicates are equivalent at every
    budget. -/
theorem intrinsicFiniteComplementSeparatesAt_iff_finiteTagSeparatesAt
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) (n : Nat) :
    IntrinsicFiniteComplementSeparatesAt D x y n <->
      FiniteTagSeparatesAt D x y n := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨E.toFiniteTagAlg, ?_⟩
    intro hEq
    apply hE
    apply E.encode_injective
    rw [← E.interp_toFiniteTagAlg x,
      ← E.interp_toFiniteTagAlg y]
    exact hEq
  · rintro ⟨T, hT⟩
    exact ⟨intrinsicOfFiniteTagAlg D T, hT⟩

/-- Intrinsic finite-complement separation, independent of the canonical sum
    presentation. -/
def IntrinsicFiniteComplementSeparating
    (D : PartialAlg.{u,v} Sigma) : Prop :=
  forall {x y : Free.GeneratedAns D}, x ≠ y ->
    Exists fun n : Nat => IntrinsicFiniteComplementSeparatesAt D x y n

/-- Every generated Resolution algebra has intrinsic finite-complement
    separation. -/
theorem intrinsicFiniteComplementSeparating_theorem
    (D : PartialAlg.{u,v} Sigma) :
    IntrinsicFiniteComplementSeparating D := by
  intro x y hxy
  let n := FiniteTagProof.nodeCount D x.1 +
    FiniteTagProof.nodeCount D y.1
  exact ⟨n,
    (intrinsicFiniteComplementSeparatesAt_iff_finiteTagSeparatesAt
      D x y n).2
      (finiteTagSeparatesAt_size_bound D x y hxy)⟩

/-- Qualitative publication-facing form of intrinsic finite-complement
    separation. -/
theorem qualitativeFiniteComplementSeparating_theorem
    (D : PartialAlg.{u,v} Sigma) :
    IntrinsicFiniteComplementSeparating D :=
  intrinsicFiniteComplementSeparating_theorem D

end External
end Resolution
