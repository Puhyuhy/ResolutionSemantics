import ResolutionFreeCompletionFinal

universe u v w v' w'

namespace Resolution
namespace Diaconescu

variable {Sigma : Signature.{u}}

/-!
# The binary, one-sorted core of Diaconescu's encoding

This file adds the existence-equality sort to the generated Resolution
algebra.  It proves the binary, one-sorted analogue of the `gamma` part of
Diaconescu's persistent-liberality theorem:

* `gamma D` satisfies the existence-equality Horn axioms;
* `beta (gamma D)` is equivalent to `D` as a partial algebra;
* every partial homomorphism `D -> beta M` has a unique lift
  `gamma D -> M`.

All operations in `Sigma` are treated as partial.  The extra Horn clause for
designated total operations is therefore intentionally absent.
-/

/-- Homomorphisms of binary partial algebras preserve every defined
application.  They need not reflect undefinedness. -/
structure PartialHom
    (D : PartialAlg.{u,v} Sigma)
    (E : PartialAlg.{u,w} Sigma) where
  toFun : D.Carrier -> E.Carrier
  map_defined : forall (f : Sigma.Op) (a b c : D.Carrier),
    D.eval f a b = some c ->
      E.eval f (toFun a) (toFun b) = some (toFun c)

@[ext] theorem PartialHom.ext
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    {F G : PartialHom D E}
    (h : F.toFun = G.toFun) : F = G := by
  cases F
  cases G
  cases h
  rfl

set_option linter.checkUnivs false in
/-- A two-sorted total algebra: the data sort and the auxiliary
existence-equality sort. -/
structure EncodedAlg (Sigma : Signature.{u}) where
  Data : Type v
  Truth : Type w
  op : Sigma.Op -> Data -> Data -> Data
  existenceEq : Data -> Data -> Truth
  trueValue : Truth

/-- The three Horn conditions relevant when all data operations are partial.
They are clauses 2--4 of the signature encoding in Diaconescu's paper. -/
structure SatisfiesGamma
    (M : EncodedAlg.{u,v,w} Sigma) : Prop where
  defined_left : forall x y : M.Data,
    M.existenceEq x y = M.trueValue ->
      M.existenceEq x x = M.trueValue
  equality_sound : forall x y : M.Data,
    M.existenceEq x y = M.trueValue -> x = y
  operation_strict : forall (f : Sigma.Op) (x y : M.Data),
    M.existenceEq (M.op f x y) (M.op f x y) = M.trueValue ->
      M.existenceEq x x = M.trueValue /\
        M.existenceEq y y = M.trueValue

/-- Recover the partial data algebra from an encoded total algebra. -/
noncomputable def beta
    (M : EncodedAlg.{u,v,w} Sigma) : PartialAlg.{u,v} Sigma := by
  classical
  exact
    { Carrier := {x : M.Data // M.existenceEq x x = M.trueValue}
      eval := fun f x y =>
        let z := M.op f x.1 y.1
        if hz : M.existenceEq z z = M.trueValue then
          some ⟨z, hz⟩
        else
          none }

/-- A computation in `beta M` is defined with result `z` exactly when the
underlying total operation has data value `z`. -/
theorem beta_eval_eq_some_iff
    (M : EncodedAlg.{u,v,w} Sigma)
    (f : Sigma.Op)
    (x y z : {x : M.Data // M.existenceEq x x = M.trueValue}) :
    (beta M).eval f x y = some z <->
      M.op f x.1 y.1 = z.1 := by
  classical
  change
    (if hz : M.existenceEq (M.op f x.1 y.1) (M.op f x.1 y.1) =
        M.trueValue then
      some ⟨M.op f x.1 y.1, hz⟩
    else none) = some z <->
      M.op f x.1 y.1 = z.1
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  · rename_i hz
    constructor
    · simp
    · intro hop
      apply False.elim
      apply hz
      simpa [hop] using z.property

/-- Undefinedness in `beta M` is exactly failure of the total result to be
marked as existent. -/
theorem beta_eval_eq_none_iff
    (M : EncodedAlg.{u,v,w} Sigma)
    (f : Sigma.Op)
    (x y : {x : M.Data // M.existenceEq x x = M.trueValue}) :
    (beta M).eval f x y = none <->
      Not (M.existenceEq (M.op f x.1 y.1) (M.op f x.1 y.1) =
        M.trueValue) := by
  classical
  unfold beta
  dsimp
  by_cases hz :
      M.existenceEq (M.op f x.1 y.1) (M.op f x.1 y.1) = M.trueValue
  · simp [hz]
  · simp [hz]

/-- Homomorphisms of encoded total algebras. -/
structure EncodedHom
    (M : EncodedAlg.{u,v,w} Sigma)
    (N : EncodedAlg.{u,v',w'} Sigma) where
  dataMap : M.Data -> N.Data
  truthMap : M.Truth -> N.Truth
  map_op : forall (f : Sigma.Op) (x y : M.Data),
    dataMap (M.op f x y) = N.op f (dataMap x) (dataMap y)
  map_existenceEq : forall x y : M.Data,
    truthMap (M.existenceEq x y) =
      N.existenceEq (dataMap x) (dataMap y)
  map_true : truthMap M.trueValue = N.trueValue

@[ext] theorem EncodedHom.ext
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,v',w'} Sigma}
    {F G : EncodedHom M N}
    (hData : F.dataMap = G.dataMap)
    (hTruth : F.truthMap = G.truthMap) : F = G := by
  cases F
  cases G
  cases hData
  cases hTruth
  rfl

/-- The action of an encoded homomorphism on the defined data elements. -/
def betaMap
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,v',w'} Sigma}
    (F : EncodedHom M N) : (beta M).Carrier -> (beta N).Carrier :=
  fun x =>
    ⟨F.dataMap x.1, by
      calc
        N.existenceEq (F.dataMap x.1) (F.dataMap x.1) =
            F.truthMap (M.existenceEq x.1 x.1) :=
          (F.map_existenceEq x.1 x.1).symm
        _ = F.truthMap M.trueValue := congrArg F.truthMap x.property
        _ = N.trueValue := F.map_true⟩

/-- `beta` sends encoded homomorphisms to partial homomorphisms. -/
noncomputable def betaHom
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,v',w'} Sigma}
    (F : EncodedHom M N) : PartialHom (beta M) (beta N) where
  toFun := betaMap F
  map_defined := by
    intro f x y z hEval
    apply (beta_eval_eq_some_iff N f (betaMap F x) (betaMap F y)
      (betaMap F z)).2
    change N.op f (F.dataMap x.1) (F.dataMap y.1) = F.dataMap z.1
    rw [<- F.map_op]
    exact congrArg F.dataMap ((beta_eval_eq_some_iff M f x y z).1 hEval)

/-- Two generated data values denote the same defined old value. -/
def SameOld
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : Prop :=
  Exists fun a : D.Carrier =>
    x = Free.generatedOld D a /\ y = Free.generatedOld D a

/-- A pair which is not the diagonal occurrence of a defined old value. -/
structure Failure
    (D : PartialAlg.{u,v} Sigma) where
  left : Free.GeneratedAns D
  right : Free.GeneratedAns D
  not_same_old : Not (SameOld D left right)

/-- The auxiliary carrier in `gamma D`: one true value and exactly one
failure value for every pair outside the old diagonal. -/
inductive GammaTruth
    (D : PartialAlg.{u,v} Sigma) where
  | trueValue
  | failure (p : Failure D)

/-- Existence equality in the canonical encoded algebra. -/
noncomputable def gammaExistenceEq
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) : GammaTruth D := by
  classical
  by_cases h : SameOld D x y
  · exact .trueValue
  · exact .failure ⟨x, y, h⟩

theorem gammaExistenceEq_eq_true_iff
    (D : PartialAlg.{u,v} Sigma)
    (x y : Free.GeneratedAns D) :
    gammaExistenceEq D x y = GammaTruth.trueValue <-> SameOld D x y := by
  classical
  by_cases h : SameOld D x y
  · simp [gammaExistenceEq, h]
  · simp [gammaExistenceEq, h]

@[simp] theorem gammaExistenceEq_failure
    (D : PartialAlg.{u,v} Sigma)
    (p : Failure D) :
    gammaExistenceEq D p.left p.right = GammaTruth.failure p := by
  classical
  cases p with
  | mk x y h => simp [gammaExistenceEq, h]

/-- Diaconescu's canonical total encoding, specialized to one data sort and
binary partial operations. -/
noncomputable def gamma
    (D : PartialAlg.{u,v} Sigma) :
    EncodedAlg.{u, max u v, max u v} Sigma where
  Data := Free.GeneratedAns D
  Truth := GammaTruth D
  op := Free.generatedOp D
  existenceEq := gammaExistenceEq D
  trueValue := GammaTruth.trueValue

private theorem liftOp_eq_old_inputs
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    {x y : RawAns Sigma D.Carrier}
    {c : D.Carrier}
    (h : D.liftOp f x y = RawAns.old c) :
    Exists fun a : D.Carrier => Exists fun b : D.Carrier =>
      x = RawAns.old a /\ y = RawAns.old b := by
  cases x with
  | old a =>
      cases y with
      | old b => exact ⟨a, b, rfl, rfl⟩
      | susp g l r => simp [PartialAlg.liftOp] at h
  | susp g l r =>
      cases y <;> simp [PartialAlg.liftOp] at h

private theorem generatedOp_eq_old_inputs
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    {x y : Free.GeneratedAns D}
    {c : D.Carrier}
    (h : Free.generatedOp D f x y = Free.generatedOld D c) :
    Exists fun a : D.Carrier => Exists fun b : D.Carrier =>
      x = Free.generatedOld D a /\ y = Free.generatedOld D b := by
  have hval := congrArg Subtype.val h
  change D.liftOp f x.1 y.1 = RawAns.old c at hval
  rcases liftOp_eq_old_inputs D f hval with ⟨a, b, hx, hy⟩
  refine ⟨a, b, ?_, ?_⟩
  · apply Subtype.ext
    exact hx
  · apply Subtype.ext
    exact hy

/-- The canonical encoding satisfies the Horn axioms `Gamma`. -/
theorem gamma_satisfiesGamma
    (D : PartialAlg.{u,v} Sigma) : SatisfiesGamma (gamma D) := by
  constructor
  · intro x y hxy
    apply (gammaExistenceEq_eq_true_iff D x x).2
    rcases (gammaExistenceEq_eq_true_iff D x y).1 hxy with ⟨a, hx, hy⟩
    exact ⟨a, hx, hx⟩
  · intro x y hxy
    rcases (gammaExistenceEq_eq_true_iff D x y).1 hxy with ⟨a, hx, hy⟩
    exact hx.trans hy.symm
  · intro f x y hop
    rcases (gammaExistenceEq_eq_true_iff D
      (Free.generatedOp D f x y) (Free.generatedOp D f x y)).1 hop with
      ⟨c, hc, _⟩
    rcases generatedOp_eq_old_inputs D f hc with ⟨a, b, hx, hy⟩
    constructor
    · apply (gammaExistenceEq_eq_true_iff D x x).2
      exact ⟨a, hx, hx⟩
    · apply (gammaExistenceEq_eq_true_iff D y y).2
      exact ⟨b, hy, hy⟩

/-- The old carrier embedded in the defined part of `gamma D`. -/
noncomputable def betaGammaEmbed
    (D : PartialAlg.{u,v} Sigma) : D.Carrier -> (beta (gamma D)).Carrier :=
  fun a =>
    ⟨Free.generatedOld D a,
      (gammaExistenceEq_eq_true_iff D
        (Free.generatedOld D a) (Free.generatedOld D a)).2
          ⟨a, rfl, rfl⟩⟩

theorem betaGammaEmbed_injective
    (D : PartialAlg.{u,v} Sigma) :
    Function.Injective (betaGammaEmbed D) := by
  intro a b hab
  apply Free.generatedOld_injective D
  exact congrArg Subtype.val hab

theorem betaGammaEmbed_surjective
    (D : PartialAlg.{u,v} Sigma) :
    Function.Surjective (betaGammaEmbed D) := by
  intro x
  rcases (gammaExistenceEq_eq_true_iff D x.1 x.1).1 x.property with
    ⟨a, hx, _⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact hx.symm

/-- A small equivalence record, kept local to the dependency-free project. -/
structure CarrierEquiv (A : Type v) (B : Type w) where
  toFun : A -> B
  invFun : B -> A
  left_inv : forall a : A, invFun (toFun a) = a
  right_inv : forall b : B, toFun (invFun b) = b

namespace CarrierEquiv

noncomputable def ofBijective
    {A : Type v} {B : Type w}
    (f : A -> B)
    (hf : Function.Injective f /\ Function.Surjective f) : CarrierEquiv A B where
  toFun := f
  invFun := fun b => Classical.choose (hf.2 b)
  left_inv := by
    intro a
    apply hf.1
    exact Classical.choose_spec (hf.2 (f a))
  right_inv := by
    intro b
    exact Classical.choose_spec (hf.2 b)

end CarrierEquiv

/-- The carrier of `beta (gamma D)` is canonically equivalent to the old
partial carrier. -/
noncomputable def betaGammaEquiv
    (D : PartialAlg.{u,v} Sigma) :
    CarrierEquiv D.Carrier (beta (gamma D)).Carrier :=
  CarrierEquiv.ofBijective (betaGammaEmbed D)
    ⟨betaGammaEmbed_injective D, betaGammaEmbed_surjective D⟩

/-- The carrier equivalence also preserves the partial evaluator exactly. -/
theorem betaGamma_eval
    (D : PartialAlg.{u,v} Sigma)
    (f : Sigma.Op)
    (a b : D.Carrier) :
    (beta (gamma D)).eval f (betaGammaEmbed D a) (betaGammaEmbed D b) =
      Option.map (betaGammaEmbed D) (D.eval f a b) := by
  classical
  cases hEval : D.eval f a b with
  | none =>
      simp only [Option.map_none]
      have hNot : Not (SameOld D
          (Free.generatedOp D f (Free.generatedOld D a)
            (Free.generatedOld D b))
          (Free.generatedOp D f (Free.generatedOld D a)
            (Free.generatedOld D b))) := by
        intro hs
        rcases hs with ⟨c, hc, _⟩
        have hval := congrArg Subtype.val hc
        change D.liftOp f (RawAns.old a) (RawAns.old b) = RawAns.old c at hval
        simp [PartialAlg.liftOp, hEval] at hval
      apply (beta_eval_eq_none_iff (gamma D) f
        (betaGammaEmbed D a) (betaGammaEmbed D b)).2
      change Not (gammaExistenceEq D
        (Free.generatedOp D f (Free.generatedOld D a)
          (Free.generatedOld D b))
        (Free.generatedOp D f (Free.generatedOld D a)
          (Free.generatedOld D b)) = GammaTruth.trueValue)
      intro hz
      exact hNot ((gammaExistenceEq_eq_true_iff D _ _).1 hz)
  | some c =>
      apply (beta_eval_eq_some_iff (gamma D) f
        (betaGammaEmbed D a) (betaGammaEmbed D b)
        (betaGammaEmbed D c)).2
      exact Free.generatedOp_old_of_defined D f a b c hEval

/-- A compact partial-algebra equivalence record. -/
structure PartialAlgEquiv
    (D : PartialAlg.{u,v} Sigma)
    (E : PartialAlg.{u,w} Sigma) where
  carrierEquiv : CarrierEquiv D.Carrier E.Carrier
  map_eval : forall (f : Sigma.Op) (a b : D.Carrier),
    E.eval f (carrierEquiv.toFun a) (carrierEquiv.toFun b) =
      Option.map carrierEquiv.toFun (D.eval f a b)

/-- `beta (gamma D)` recovers `D` up to canonical partial-algebra
equivalence. -/
noncomputable def betaGammaPartialAlgEquiv
    (D : PartialAlg.{u,v} Sigma) :
    PartialAlgEquiv D (beta (gamma D)) where
  carrierEquiv := betaGammaEquiv D
  map_eval := betaGamma_eval D

private noncomputable def compatibleTarget
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M)) : Free.CompatibleAlg D where
  Carrier := M.Data
  embed := fun a => (h.toFun a).1
  op := M.op
  preserve := by
    intro f a b c hEval
    exact (beta_eval_eq_some_iff M f (h.toFun a) (h.toFun b)
      (h.toFun c)).1 (h.map_defined f a b c hEval)

private noncomputable def liftData
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M)) : Free.GeneratedAns D -> M.Data :=
  Free.CompatibleAlg.interp D (compatibleTarget D M h)

@[simp] private theorem liftData_old
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M))
    (a : D.Carrier) :
    liftData D M h (Free.generatedOld D a) = (h.toFun a).1 :=
  Free.CompatibleAlg.interp_generatedOld D (compatibleTarget D M h) a

private theorem liftData_op
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M))
    (f : Sigma.Op)
    (x y : Free.GeneratedAns D) :
    liftData D M h (Free.generatedOp D f x y) =
      M.op f (liftData D M h x) (liftData D M h y) :=
  Free.CompatibleAlg.interp_generatedOp D (compatibleTarget D M h) f x y

private noncomputable def liftTruth
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M)) : GammaTruth D -> M.Truth
  | .trueValue => M.trueValue
  | .failure p =>
      M.existenceEq (liftData D M h p.left) (liftData D M h p.right)

/-- The canonical lift supplied by the free generated algebra. -/
noncomputable def gammaLift
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M)) : EncodedHom (gamma D) M where
  dataMap := liftData D M h
  truthMap := liftTruth D M h
  map_op := liftData_op D M h
  map_existenceEq := by
    intro x y
    classical
    change
      liftTruth D M h (gammaExistenceEq D x y) =
        M.existenceEq (liftData D M h x) (liftData D M h y)
    by_cases hxy : SameOld D x y
    · rcases hxy with ⟨a, hx, hy⟩
      subst x
      subst y
      rw [(gammaExistenceEq_eq_true_iff D
        (Free.generatedOld D a) (Free.generatedOld D a)).2
          ⟨a, rfl, rfl⟩]
      change M.trueValue =
        M.existenceEq (liftData D M h (Free.generatedOld D a))
          (liftData D M h (Free.generatedOld D a))
      simpa using (h.toFun a).property.symm
    · simp [gammaExistenceEq, hxy, liftTruth]
  map_true := rfl

theorem gammaLift_agrees
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M))
    (a : D.Carrier) :
    betaMap (gammaLift D M h) (betaGammaEmbed D a) = h.toFun a := by
  apply Subtype.ext
  exact liftData_old D M h a

private noncomputable def compatibleHomOfEncodedHom
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (h : PartialHom D (beta M))
    (G : EncodedHom (gamma D) M)
    (hG : forall a : D.Carrier,
      betaMap G (betaGammaEmbed D a) = h.toFun a) :
    Free.CompatibleHom D (compatibleTarget D M h) where
  toFun := G.dataMap
  map_old := by
    intro a
    exact congrArg Subtype.val (hG a)
  map_op := G.map_op

/-- Binary, one-sorted persistent liberality: after the canonical
identification `beta (gamma D) ≃ D`, every partial homomorphism into `beta M`
has a unique encoded lift out of `gamma D`. -/
theorem gamma_persistent_liberality
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,v',w'} Sigma)
    (_hM : SatisfiesGamma M)
    (h : PartialHom D (beta M)) :
    Exists fun F : EncodedHom (gamma D) M =>
      (forall a : D.Carrier,
        betaMap F (betaGammaEmbed D a) = h.toFun a) /\
      forall G : EncodedHom (gamma D) M,
        (forall a : D.Carrier,
          betaMap G (betaGammaEmbed D a) = h.toFun a) -> G = F := by
  refine ⟨gammaLift D M h, gammaLift_agrees D M h, ?_⟩
  intro G hG
  let CG := compatibleHomOfEncodedHom D M h G hG
  have hCompatible := Free.compatibleHom_unique D (compatibleTarget D M h) CG
  have hData : G.dataMap = liftData D M h := by
    exact congrArg Free.CompatibleHom.toFun hCompatible
  apply EncodedHom.ext hData
  funext t
  cases t with
  | trueValue =>
      exact G.map_true
  | failure p =>
      have hMap := G.map_existenceEq p.left p.right
      change G.truthMap (gammaExistenceEq D p.left p.right) =
        M.existenceEq (G.dataMap p.left) (G.dataMap p.right) at hMap
      rw [gammaExistenceEq_failure D p] at hMap
      change G.truthMap (GammaTruth.failure p) =
        liftTruth D M h (GammaTruth.failure p)
      change G.truthMap (GammaTruth.failure p) =
        M.existenceEq (liftData D M h p.left) (liftData D M h p.right)
      rw [hMap, hData]

end Diaconescu
end Resolution
