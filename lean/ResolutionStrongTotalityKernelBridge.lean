import ResolutionStrongTotalityRepresentationInvariant

/-!
# Bridge from Strong Totality to the Resolution kernel

Strong Totality for arbitrary specifications should extend the concrete
Resolution semantics already present in the repository rather than forming a
parallel theory.  This module supplies the first direct bridge.

For a kernel expression `e`, consider the mathematical specification whose
ordinary candidates are old carrier values and whose acceptance predicate says
that kernel resolution of `e` is exactly `.old a`.  If kernel resolution
succeeds with an old value, that value becomes a realized Strong Totality
answer.  If it produces a suspension, the complete suspension node is retained
as structured residual provenance.

Hence the existing evaluator `Expr.res` factors through a provenance-preserving
Strong Totality answer.  Forgetting residual provenance gives the minimal
Strong Totality semantics, while decoding the structured answer recovers the
kernel result exactly.
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

/-- The specification represented by a concrete kernel expression: an ordinary
candidate `a` is accepted exactly when kernel resolution computes the old value
`.old a`. -/
def kernelExprSpecification
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) : Specification.{v} where
  Candidate := D.Carrier
  accepts := fun a => Expr.res D e = .old a

/-- Interpret one already-exposed raw kernel result as a structured Strong
Totality answer.  The equality certificate is separated from the case split so
that downstream reasoning need not eliminate through a dependent `match`. -/
def kernelExprResolutionFrom
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (r : RawAns Sigma D.Carrier)
    (h : Expr.res D e = r) :
    ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier) :=
  match r with
  | .old a => .realized a h
  | .susp op x y => .residual ⟨op, x, y⟩

@[simp] theorem kernelExprResolutionFrom_old
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (a : D.Carrier)
    (h : Expr.res D e = .old a) :
    kernelExprResolutionFrom D e (.old a) h =
      (.realized a h : ResolutionAnswerWith
        (kernelExprSpecification D e)
        (KernelResidual Sigma D.Carrier)) := by
  rfl

@[simp] theorem kernelExprResolutionFrom_susp
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier)
    (op : Sigma.Op)
    (x y : RawAns Sigma D.Carrier)
    (h : Expr.res D e = .susp op x y) :
    kernelExprResolutionFrom D e (.susp op x y) h =
      (.residual ⟨op, x, y⟩ : ResolutionAnswerWith
        (kernelExprSpecification D e)
        (KernelResidual Sigma D.Carrier)) := by
  rfl

/-- The provenance-preserving Strong Totality answer associated canonically to
a kernel expression. -/
def kernelExprResolution
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier) :=
  kernelExprResolutionFrom D e (Expr.res D e) rfl

/-- Decode the structured Strong Totality answer back into the native kernel
answer syntax. -/
def decodeKernelExprResolution
    {D : PartialAlg.{u,v} Sigma}
    {e : Expr Sigma D.Carrier} :
    ResolutionAnswerWith
      (kernelExprSpecification D e)
      (KernelResidual Sigma D.Carrier) ->
    RawAns Sigma D.Carrier
  | .realized a _ => .old a
  | .residual r => r.toRawAns

/-- The Strong Totality bridge is lossless: decoding its structured answer
recovers exactly the existing kernel evaluator result. -/
theorem decode_kernelExprResolution
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    decodeKernelExprResolution (kernelExprResolution D e) = Expr.res D e := by
  unfold kernelExprResolution
  cases h : Expr.res D e with
  | old a =>
      have hp : rfl = h := Subsingleton.elim _ _
      rw [hp]
      rfl
  | susp op x y =>
      rfl

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
  unfold kernelExprResolution
  rw [h]
  have hp : rfl = h := Subsingleton.elim _ _
  rw [hp]
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
  unfold kernelExprResolution
  rw [h]
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

/-- Interpret one already-exposed partial operation result as a structured
Strong Totality answer. -/
def kernelOperationResolutionFrom
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier)
    (r : Option D.Carrier)
    (h : D.eval op a b = r) :
    ResolutionAnswerWith
      (kernelOperationSpecification D op a b)
      (KernelResidual Sigma D.Carrier) :=
  match r with
  | some c => .realized c h
  | none => .residual ⟨op, .old a, .old b⟩

/-- A one-step partial operation has a canonical provenance-preserving Strong
Totality answer. -/
def kernelOperationResolution
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) :
    ResolutionAnswerWith
      (kernelOperationSpecification D op a b)
      (KernelResidual Sigma D.Carrier) :=
  kernelOperationResolutionFrom D op a b (D.eval op a b) rfl

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
  unfold kernelOperationResolution
  rw [h]
  have hp : rfl = h := Subsingleton.elim _ _
  rw [hp]
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
  unfold kernelOperationResolution
  rw [h]
  rfl

/-- Decoding the one-step Strong Totality answer agrees exactly with the
existing lifted kernel operation on old arguments. -/
theorem decode_kernelOperationResolution
    (D : PartialAlg.{u,v} Sigma)
    (op : Sigma.Op)
    (a b : D.Carrier) :
    decodeKernelExprResolution
      (e := Expr.app op (Expr.val a) (Expr.val b))
      (match h : D.eval op a b with
       | some c =>
           (.realized c (by
             change D.liftOp op (.old a) (.old b) = .old c
             unfold PartialAlg.liftOp
             rw [h]) : ResolutionAnswerWith
             (kernelExprSpecification D
               (Expr.app op (Expr.val a) (Expr.val b)))
             (KernelResidual Sigma D.Carrier))
       | none =>
           (.residual ⟨op, .old a, .old b⟩ : ResolutionAnswerWith
             (kernelExprSpecification D
               (Expr.app op (Expr.val a) (Expr.val b)))
             (KernelResidual Sigma D.Carrier))) =
      D.liftOp op (.old a) (.old b) := by
  cases h : D.eval op a b with
  | none =>
      unfold PartialAlg.liftOp
      rw [h]
      rfl
  | some c =>
      unfold PartialAlg.liftOp
      rw [h]
      rfl

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
