import ResolutionStrongTotalityRepresentationInvariant

/-!
# Bridge from Strong Totality to the Resolution kernel

Strong Totality for arbitrary specifications should extend the concrete
Resolution semantics already present in the repository rather than forming a
parallel theory.  This module supplies a direct bridge.

For a kernel expression `e`, consider the mathematical specification whose
ordinary candidates are old carrier values and whose acceptance predicate says
that kernel resolution of `e` is exactly `.old a`.  If kernel resolution
succeeds with an old value, that value becomes a realized Strong Totality
answer.  If it produces a suspension, the complete suspension node is retained
as structured residual provenance.

The raw result and its equality certificate are packaged as one observation.
This avoids dependent rewrites entirely: transport between equivalent
observations is ordinary equality of subtypes, while the semantic case split is
performed only after the observation has been fixed.
-/

universe u v

namespace Resolution
namespace StrongTotality

variable {Sigma : Signature.{u}}

/-- The residual vocabulary needed to represent one kernel suspension without
loss of provenance. -/
structure KernelResidual (Sigma : Signature.{u}) (A : Type v) where
  op : Sigma.Op
  left : RawAns Sigma A
  right : RawAns Sigma A

namespace KernelResidual

/-- Re-embed structured kernel residual provenance into the native `RawAns`
syntax. -/
def toRawAns
    {Sigma : Signature.{u}} {A : Type v}
    (r : KernelResidual Sigma A) : RawAns Sigma A :=
  .susp r.op r.left r.right

end KernelResidual

/-- The specification represented by a concrete kernel expression. -/
def kernelExprSpecification
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) : Specification.{v} where
  Candidate := D.Carrier
  accepts := fun a => Expr.res D e = .old a

/-- A raw expression result together with the certificate that it is exactly
the result of the kernel evaluator. -/
abbrev KernelExprObservation
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :=
  { r : RawAns Sigma D.Carrier // Expr.res D e = r }

/-- The canonical observation of a kernel expression. -/
def canonicalKernelExprObservation
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) : KernelExprObservation D e :=
  ⟨Expr.res D e, rfl⟩

/-- Interpret a fixed kernel observation as a structured Strong Totality
answer. -/
def kernelExprResolutionFromObservation
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    KernelExprObservation D e ->
      ResolutionAnswerWith
        (kernelExprSpecification D e)
        (KernelResidual Sigma D.Carrier)
  | ⟨.old a, h⟩ => .realized a h
  | ⟨.susp op x y, _⟩ => .residual ⟨op, x, y⟩

/-- The provenance-preserving Strong Totality answer associated canonically to
a kernel expression. -/
def kernelExprResolution
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier) :=
  kernelExprResolutionFromObservation D e
    (canonicalKernelExprObservation D e)

/-- Decode the structured Strong Totality answer back into native kernel
syntax. -/
def decodeKernelExprResolution
    {D : PartialAlg.{u,v} Sigma}
    {e : Expr Sigma D.Carrier} :
    ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier) ->
    RawAns Sigma D.Carrier
  | .realized a _ => .old a
  | .residual r => r.toRawAns

/-- Decoding an answer obtained from any certified observation returns exactly
the observed raw result. -/
theorem decode_kernelExprResolutionFromObservation
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (o : KernelExprObservation D e) :
    decodeKernelExprResolution
        (kernelExprResolutionFromObservation D e o) = o.1 := by
  cases o with
  | mk r h =>
      cases r <;> rfl

/-- The Strong Totality bridge is lossless. -/
theorem decode_kernelExprResolution
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    decodeKernelExprResolution (kernelExprResolution D e) = Expr.res D e := by
  exact decode_kernelExprResolutionFromObservation D e
    (canonicalKernelExprObservation D e)

/-- If kernel resolution computes an old value, the bridge produces exactly the
corresponding realized Strong Totality solution. -/
theorem kernelExprResolution_of_old
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (a : D.Carrier)
    (h : Expr.res D e = .old a) :
    kernelExprResolution D e =
      (.realized a h : ResolutionAnswerWith
        (kernelExprSpecification D e)
        (KernelResidual Sigma D.Carrier)) := by
  have ho :
      canonicalKernelExprObservation D e =
        (⟨.old a, h⟩ : KernelExprObservation D e) := by
    apply Subtype.ext
    exact h
  unfold kernelExprResolution
  rw [ho]
  rfl

/-- If kernel resolution suspends, the bridge records precisely that suspension
node as residual provenance. -/
theorem kernelExprResolution_of_susp
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (op : Sigma.Op)
    (x y : RawAns Sigma D.Carrier)
    (h : Expr.res D e = .susp op x y) :
    kernelExprResolution D e =
      (.residual ⟨op, x, y⟩ : ResolutionAnswerWith
        (kernelExprSpecification D e)
        (KernelResidual Sigma D.Carrier)) := by
  have ho :
      canonicalKernelExprObservation D e =
        (⟨.susp op x y, h⟩ : KernelExprObservation D e) := by
    apply Subtype.ext
    exact h
  unfold kernelExprResolution
  rw [ho]
  rfl

/-- Forgetting suspension provenance yields the minimal Strong Totality answer
for the expression specification. -/
def kernelExprMinimalResolution
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    ResolutionAnswer (kernelExprSpecification D e) :=
  coarsenResidual (kernelExprResolution D e)

/-- An old kernel result remains realized after provenance is forgotten. -/
theorem kernelExprMinimalResolution_of_old
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (a : D.Carrier)
    (h : Expr.res D e = .old a) :
    kernelExprMinimalResolution D e = realizeSolution
      (⟨a, h⟩ : Specification.Solution (kernelExprSpecification D e)) := by
  unfold kernelExprMinimalResolution
  rw [kernelExprResolution_of_old D e a h]
  rfl

/-- A suspended kernel result becomes exactly the unique minimal residual after
provenance is forgotten. -/
theorem kernelExprMinimalResolution_of_susp
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (op : Sigma.Op)
    (x y : RawAns Sigma D.Carrier)
    (h : Expr.res D e = .susp op x y) :
    kernelExprMinimalResolution D e =
      (ResolutionAnswer.residual :
        ResolutionAnswer (kernelExprSpecification D e)) := by
  unfold kernelExprMinimalResolution
  rw [kernelExprResolution_of_susp D e op x y h]
  rfl

/-! ## One-step partial operations -/

/-- Specification of an old-result application of one partial algebra
operation. -/
def kernelOperationSpecification
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) : Specification.{v} where
  Candidate := D.Carrier
  accepts := fun c => D.eval op a b = some c

/-- An observed partial-operation result together with its kernel certificate. -/
abbrev KernelOperationObservation
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) :=
  { r : Option D.Carrier // D.eval op a b = r }

/-- Canonical observation of a one-step partial operation. -/
def canonicalKernelOperationObservation
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) : KernelOperationObservation D op a b :=
  ⟨D.eval op a b, rfl⟩

/-- Interpret a fixed one-step observation as structured Strong Totality data. -/
def kernelOperationResolutionFromObservation
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) :
    KernelOperationObservation D op a b ->
      ResolutionAnswerWith
        (kernelOperationSpecification D op a b)
        (KernelResidual Sigma D.Carrier)
  | ⟨some c, h⟩ => .realized c h
  | ⟨none, _⟩ => .residual ⟨op, .old a, .old b⟩

/-- Canonical provenance-preserving Strong Totality answer for one operation. -/
def kernelOperationResolution
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) :
    ResolutionAnswerWith
      (kernelOperationSpecification D op a b)
      (KernelResidual Sigma D.Carrier) :=
  kernelOperationResolutionFromObservation D op a b
    (canonicalKernelOperationObservation D op a b)

/-- Successful old operations are conservatively embedded as realized answers. -/
theorem kernelOperationResolution_some
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b c : D.Carrier)
    (h : D.eval op a b = some c) :
    kernelOperationResolution D op a b =
      (.realized c h : ResolutionAnswerWith
        (kernelOperationSpecification D op a b)
        (KernelResidual Sigma D.Carrier)) := by
  have ho :
      canonicalKernelOperationObservation D op a b =
        (⟨some c, h⟩ : KernelOperationObservation D op a b) := by
    apply Subtype.ext
    exact h
  unfold kernelOperationResolution
  rw [ho]
  rfl

/-- Undefined old operations retain exactly the native kernel suspension as
structured residual provenance. -/
theorem kernelOperationResolution_none
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier)
    (h : D.eval op a b = none) :
    kernelOperationResolution D op a b =
      (.residual ⟨op, .old a, .old b⟩ : ResolutionAnswerWith
        (kernelOperationSpecification D op a b)
        (KernelResidual Sigma D.Carrier)) := by
  have ho :
      canonicalKernelOperationObservation D op a b =
        (⟨none, h⟩ : KernelOperationObservation D op a b) := by
    apply Subtype.ext
    exact h
  unfold kernelOperationResolution
  rw [ho]
  rfl

/-- Decode one-step operation semantics into native `RawAns`. -/
def decodeKernelOperationResolution
    {D : PartialAlg.{u,v} Sigma}
    {op : Sigma.Op}
    {a b : D.Carrier} :
    ResolutionAnswerWith
      (kernelOperationSpecification D op a b)
      (KernelResidual Sigma D.Carrier) ->
    RawAns Sigma D.Carrier
  | .realized c _ => .old c
  | .residual r => r.toRawAns

/-- Decoding the one-step Strong Totality answer agrees exactly with the
existing lifted kernel operation on old arguments. -/
theorem decode_kernelOperationResolution
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) :
    decodeKernelOperationResolution (kernelOperationResolution D op a b) =
      D.liftOp op (.old a) (.old b) := by
  cases h : D.eval op a b with
  | none =>
      rw [kernelOperationResolution_none D op a b h]
      unfold decodeKernelOperationResolution KernelResidual.toRawAns
      unfold PartialAlg.liftOp
      change
        (match D.eval op a b with
         | some c => RawAns.old c
         | none => RawAns.susp op (.old a) (.old b)) =
          RawAns.susp op (.old a) (.old b)
      rw [h]
  | some c =>
      rw [kernelOperationResolution_some D op a b c h]
      unfold decodeKernelOperationResolution
      unfold PartialAlg.liftOp
      change
        (RawAns.old c : RawAns Sigma D.Carrier) =
          (match D.eval op a b with
           | some d => RawAns.old d
           | none => RawAns.susp op (.old a) (.old b))
      rw [h]

/-- Conceptual bridge theorem: the kernel evaluator is already a structured
Strong Totality semantics for the expression specification, with suspension
syntax serving as residual provenance. -/
theorem kernel_isStructuredStrongTotality
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    Nonempty (ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier)) :=
  ⟨kernelExprResolution D e⟩

end StrongTotality
end Resolution
