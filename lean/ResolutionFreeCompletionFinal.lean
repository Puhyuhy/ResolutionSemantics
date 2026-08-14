import ResolutionFiniteTagProof

universe u v w

namespace Resolution
namespace Free

variable {Sigma : Signature.{u}}

/-- A total algebra equipped with a map from the old partial carrier and
    preserving every old-defined application. Unlike `TotalAlg`, the old map
    need not be injective. This is the natural target notion for the ordinary
    free-completion universal property. -/
structure CompatibleAlg (D : PartialAlg.{u,v} Sigma) where
  Carrier : Type w
  embed : D.Carrier -> Carrier
  op : Sigma.Op -> Carrier -> Carrier -> Carrier
  preserve : forall (f : Sigma.Op) (a b c : D.Carrier),
    D.eval f a b = some c ->
      op f (embed a) (embed b) = embed c

namespace CompatibleAlg

variable (D : PartialAlg.{u,v} Sigma) (T : CompatibleAlg.{u,v,w} D)

def foldRaw : RawAns Sigma D.Carrier -> T.Carrier
  | .old a => T.embed a
  | .susp f x y => T.op f (foldRaw x) (foldRaw y)

def interp (x : GeneratedAns D) : T.Carrier :=
  foldRaw D T x.1

theorem foldRaw_liftOp
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
              simp [PartialAlg.liftOp, hEval, foldRaw,
                T.preserve f a b c hEval]
      | susp g l r =>
          simp [PartialAlg.liftOp, foldRaw]
  | susp g l r =>
      cases y <;> simp [PartialAlg.liftOp, foldRaw]

@[simp] theorem interp_generatedOld
    (a : D.Carrier) :
    interp D T (generatedOld D a) = T.embed a := by
  rfl

theorem interp_generatedOp
    (f : Sigma.Op)
    (x y : GeneratedAns D) :
    interp D T (generatedOp D f x y) =
      T.op f (interp D T x) (interp D T y) := by
  unfold interp
  rw [generatedOp_val]
  exact foldRaw_liftOp D T f x.1 y.1

end CompatibleAlg

def ofExpr
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) : GeneratedAns D :=
  ⟨Expr.res D e, ⟨e, rfl⟩⟩

@[simp] theorem ofExpr_val
    (D : PartialAlg.{u,v} Sigma)
    (a : D.Carrier) :
    ofExpr D (.val a) = generatedOld D a := by
  rfl

@[simp] theorem ofExpr_app
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (x y : Expr Sigma D.Carrier) :
    ofExpr D (.app f x y) =
      generatedOp D f (ofExpr D x) (ofExpr D y) := by
  apply Subtype.ext
  rfl

structure CompatibleHom
    (D : PartialAlg.{u,v} Sigma)
    (T : CompatibleAlg.{u,v,w} D) where
  toFun : GeneratedAns D -> T.Carrier
  map_old : forall a : D.Carrier,
    toFun (generatedOld D a) = T.embed a
  map_op : forall (f : Sigma.Op) (x y : GeneratedAns D),
    toFun (generatedOp D f x y) =
      T.op f (toFun x) (toFun y)

@[ext] theorem CompatibleHom.ext
    {D : PartialAlg.{u,v} Sigma}
    {T : CompatibleAlg.{u,v,w} D}
    {F G : CompatibleHom D T}
    (h : F.toFun = G.toFun) : F = G := by
  cases F
  cases G
  cases h
  rfl

noncomputable def compatibleInterpHom
    (D : PartialAlg.{u,v} Sigma)
    (T : CompatibleAlg.{u,v,w} D) : CompatibleHom D T where
  toFun := CompatibleAlg.interp D T
  map_old := CompatibleAlg.interp_generatedOld D T
  map_op := CompatibleAlg.interp_generatedOp D T

theorem compatibleHom_on_ofExpr
    (D : PartialAlg.{u,v} Sigma)
    (T : CompatibleAlg.{u,v,w} D)
    (F : CompatibleHom D T)
    (e : Expr Sigma D.Carrier) :
    F.toFun (ofExpr D e) =
      CompatibleAlg.interp D T (ofExpr D e) := by
  induction e with
  | val a =>
      simpa using F.map_old a
  | app f x y ihx ihy =>
      rw [ofExpr_app]
      rw [F.map_op, CompatibleAlg.interp_generatedOp, ihx, ihy]

theorem compatibleHom_unique
    (D : PartialAlg.{u,v} Sigma)
    (T : CompatibleAlg.{u,v,w} D)
    (F : CompatibleHom D T) :
    F = compatibleInterpHom D T := by
  apply CompatibleHom.ext
  funext x
  rcases x.property with ⟨e, he⟩
  have hx : x = ofExpr D e := by
    apply Subtype.ext
    exact he.symm
  calc
    F.toFun x = F.toFun (ofExpr D e) := congrArg F.toFun hx
    _ = CompatibleAlg.interp D T (ofExpr D e) :=
      compatibleHom_on_ofExpr D T F e
    _ = CompatibleAlg.interp D T x :=
      congrArg (CompatibleAlg.interp D T) hx.symm
    _ = (compatibleInterpHom D T).toFun x := rfl

theorem generatedAns_has_unique_compatibleHom
    (D : PartialAlg.{u,v} Sigma)
    (T : CompatibleAlg.{u,v,w} D) :
    ∃ F : CompatibleHom D T,
      ∀ G : CompatibleHom D T, G = F := by
  refine ⟨compatibleInterpHom D T, ?_⟩
  intro G
  exact compatibleHom_unique D T G

def ExprResolutionSetoid
    (D : PartialAlg.{u,v} Sigma) : Setoid (Expr Sigma D.Carrier) where
  r x y := Expr.res D x = Expr.res D y
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

def ExprResolutionQuotient
    (D : PartialAlg.{u,v} Sigma) :=
  Quotient (ExprResolutionSetoid D)

def quotientToGenerated
    (D : PartialAlg.{u,v} Sigma) :
    ExprResolutionQuotient D -> GeneratedAns D :=
  Quotient.lift
    (fun e : Expr Sigma D.Carrier => (ofExpr D e : GeneratedAns D))
    (by
      intro x y h
      apply Subtype.ext
      exact h)

@[simp] theorem quotientToGenerated_mk
    (D : PartialAlg.{u,v} Sigma)
    (e : Expr Sigma D.Carrier) :
    quotientToGenerated D
      (Quotient.mk (ExprResolutionSetoid D) e) = ofExpr D e := by
  rfl

noncomputable def generatedToQuotient
    (D : PartialAlg.{u,v} Sigma)
    (x : GeneratedAns D) : ExprResolutionQuotient D :=
  Quotient.mk (ExprResolutionSetoid D) (Classical.choose x.property)

@[simp] theorem quotientToGenerated_generatedToQuotient
    (D : PartialAlg.{u,v} Sigma)
    (x : GeneratedAns D) :
    quotientToGenerated D (generatedToQuotient D x) = x := by
  change ofExpr D (Classical.choose x.property) = x
  apply Subtype.ext
  exact Classical.choose_spec x.property

@[simp] theorem generatedToQuotient_quotientToGenerated
    (D : PartialAlg.{u,v} Sigma)
    (q : ExprResolutionQuotient D) :
    generatedToQuotient D (quotientToGenerated D q) = q := by
  refine Quotient.inductionOn q ?_
  intro e
  change Quotient.mk (ExprResolutionSetoid D)
      (Classical.choose (ofExpr D e).property) =
    Quotient.mk (ExprResolutionSetoid D) e
  apply Quotient.sound
  exact Classical.choose_spec (ofExpr D e).property

/-- The quotient presentation maps injectively to generated Answers. -/
theorem quotientToGenerated_injective
    (D : PartialAlg.{u,v} Sigma) :
    Function.Injective (quotientToGenerated D) := by
  intro q r hqr
  have h := congrArg (generatedToQuotient D) hqr
  simpa using h

/-- Every generated Answer is represented by a quotient class of expressions. -/
theorem quotientToGenerated_surjective
    (D : PartialAlg.{u,v} Sigma) :
    Function.Surjective (quotientToGenerated D) := by
  intro x
  exact ⟨generatedToQuotient D x,
    quotientToGenerated_generatedToQuotient D x⟩

end Free
end Resolution
