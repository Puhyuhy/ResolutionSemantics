import ResolutionDiaconescuManySorted

universe u v w x y z q

namespace Resolution
namespace Diaconescu
namespace ManySorted

noncomputable local instance continuationClassicalPropDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-!
# Functorial and universal structure of the many-sorted encoding

This module packages the pointwise constructions from
`ResolutionDiaconescuManySorted` into reusable structure. It deliberately
uses only the small algebraic API developed in this repository: no ambient
category-theory library is needed to state or check the functor laws and the
`gamma`--`beta` hom-set equivalence.
-/

namespace PartialHom

@[ext] theorem ext
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    {F G : PartialHom A B}
    (h : F.toFun = G.toFun) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Identity partial-algebra homomorphism. -/
def identity
    {Sigma : Signature.{u}}
    (A : PartialAlg.{u,v} Sigma) : PartialHom A A where
  toFun := fun _ value => value
  map_total := by intros; rfl
  map_partial := by intros; assumption

/-- Composition, written in categorical order: `comp g f` means `g after f`.
-/
def comp
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    {C : PartialAlg.{u,x} Sigma}
    (g : PartialHom B C)
    (f : PartialHom A B) : PartialHom A C where
  toFun := fun s value => g.toFun s (f.toFun s value)
  map_total := by
    intro op args
    calc
      g.toFun _ (f.toFun _ (A.evalTotal op args)) =
          g.toFun _ (B.evalTotal op (fun i => f.toFun _ (args i))) :=
        congrArg (g.toFun _) (f.map_total op args)
      _ = C.evalTotal op (fun i => g.toFun _ (f.toFun _ (args i))) :=
        g.map_total op (fun i => f.toFun _ (args i))
  map_partial := by
    intro op args result hEval
    exact g.map_partial op (fun i => f.toFun _ (args i))
      (f.toFun _ result) (f.map_partial op args result hEval)

@[simp] theorem identity_toFun
    {Sigma : Signature.{u}}
    (A : PartialAlg.{u,v} Sigma)
    (s : Sigma.SortId)
    (value : A.Carrier s) :
    (identity A).toFun s value = value := rfl

@[simp] theorem comp_toFun
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    {C : PartialAlg.{u,x} Sigma}
    (g : PartialHom B C)
    (f : PartialHom A B)
    (s : Sigma.SortId)
    (value : A.Carrier s) :
    (comp g f).toFun s value = g.toFun s (f.toFun s value) := rfl

theorem comp_identity
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    (f : PartialHom A B) : comp f (identity A) = f := by
  apply ext
  rfl

theorem identity_comp
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    (f : PartialHom A B) : comp (identity B) f = f := by
  apply ext
  rfl

theorem comp_assoc
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    {C : PartialAlg.{u,x} Sigma}
    {D : PartialAlg.{u,y} Sigma}
    (h : PartialHom C D)
    (g : PartialHom B C)
    (f : PartialHom A B) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  rfl

end PartialHom

namespace EncodedHom

/-- Identity encoded-algebra homomorphism. -/
def identity
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma) : EncodedHom M M where
  dataMap := fun _ value => value
  truthMap := fun value => value
  map_total := by intros; rfl
  map_partial_symbol := by intros; rfl
  map_existenceEq := by intros; rfl
  map_true := rfl

/-- Composition, written in categorical order: `comp g f` means `g after f`.
-/
def comp
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    {P : EncodedAlg.{u,z,q} Sigma}
    (g : EncodedHom N P)
    (f : EncodedHom M N) : EncodedHom M P where
  dataMap := fun s value => g.dataMap s (f.dataMap s value)
  truthMap := fun value => g.truthMap (f.truthMap value)
  map_total := by
    intro op args
    calc
      g.dataMap _ (f.dataMap _ (M.evalTotal op args)) =
          g.dataMap _ (N.evalTotal op (fun i => f.dataMap _ (args i))) :=
        congrArg (g.dataMap _) (f.map_total op args)
      _ = P.evalTotal op
          (fun i => g.dataMap _ (f.dataMap _ (args i))) :=
        g.map_total op (fun i => f.dataMap _ (args i))
  map_partial_symbol := by
    intro op args
    calc
      g.dataMap _ (f.dataMap _ (M.evalPartialSymbol op args)) =
          g.dataMap _
            (N.evalPartialSymbol op (fun i => f.dataMap _ (args i))) :=
        congrArg (g.dataMap _) (f.map_partial_symbol op args)
      _ = P.evalPartialSymbol op
          (fun i => g.dataMap _ (f.dataMap _ (args i))) :=
        g.map_partial_symbol op (fun i => f.dataMap _ (args i))
  map_existenceEq := by
    intro s left right
    calc
      g.truthMap (f.truthMap (M.existenceEq s left right)) =
          g.truthMap
            (N.existenceEq s (f.dataMap s left) (f.dataMap s right)) :=
        congrArg g.truthMap (f.map_existenceEq s left right)
      _ = P.existenceEq s
          (g.dataMap s (f.dataMap s left))
          (g.dataMap s (f.dataMap s right)) :=
        g.map_existenceEq s (f.dataMap s left) (f.dataMap s right)
  map_true := by
    calc
      g.truthMap (f.truthMap M.trueValue) = g.truthMap N.trueValue :=
        congrArg g.truthMap f.map_true
      _ = P.trueValue := g.map_true

theorem comp_identity
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (f : EncodedHom M N) : comp f (identity M) = f := by
  apply EncodedHom.ext
  · rfl
  · rfl

theorem identity_comp
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (f : EncodedHom M N) : comp (identity N) f = f := by
  apply EncodedHom.ext
  · rfl
  · rfl

end EncodedHom

/-! ## The `beta` functor laws -/

theorem betaHom_identity
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M) :
    betaHom hM hM (EncodedHom.identity M) =
      PartialHom.identity (beta M hM) := by
  apply PartialHom.ext
  funext s value
  apply Subtype.ext
  rfl

theorem betaHom_comp
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    {P : EncodedAlg.{u,z,q} Sigma}
    (hM : SatisfiesGamma M)
    (hN : SatisfiesGamma N)
    (hP : SatisfiesGamma P)
    (g : EncodedHom N P)
    (f : EncodedHom M N) :
    betaHom hM hP (EncodedHom.comp g f) =
      PartialHom.comp (betaHom hN hP g) (betaHom hM hN f) := by
  apply PartialHom.ext
  funext s value
  apply Subtype.ext
  rfl

/-! ## The hom-set equivalence induced by persistent liberality -/

/-- A dependency-free equivalence of hom-sets. -/
structure HomEquiv (A : Type v) (B : Type w) where
  toFun : A -> B
  invFun : B -> A
  left_inv : forall value, invFun (toFun value) = value
  right_inv : forall value, toFun (invFun value) = value

/-- The canonical unit map `D -> beta (gamma D)`. -/
noncomputable def betaGammaHom
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    PartialHom D (beta (gamma D) (gamma_satisfiesGamma D)) where
  toFun := betaGammaEmbed D
  map_total := by
    intro op args
    exact (betaGamma_evalTotal D op args).symm
  map_partial := by
    intro op args result hEval
    rw [betaGamma_evalPartial D op args, hEval]
    rfl

/-- Restrict an encoded map out of `gamma D` to the old partial algebra. -/
noncomputable def gammaRestrict
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (map : EncodedHom (gamma D) M) : PartialHom D (beta M hM) :=
  PartialHom.comp
    (betaHom (gamma_satisfiesGamma D) hM map)
    (betaGammaHom D)

@[simp] theorem gammaRestrict_toFun
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (map : EncodedHom (gamma D) M)
    (s : Sigma.SortId)
    (value : D.Carrier s) :
    (gammaRestrict D M hM map).toFun s value =
      betaMap map s (betaGammaEmbed D s value) := rfl

theorem gammaRestrict_gammaLift
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (hom : PartialHom D (beta M hM)) :
    gammaRestrict D M hM (gammaLift D M hM hom) = hom := by
  apply PartialHom.ext
  funext s value
  exact gammaLift_agrees D M hM hom s value

theorem gammaLift_gammaRestrict
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (map : EncodedHom (gamma D) M) :
    gammaLift D M hM (gammaRestrict D M hM map) = map := by
  rcases gamma_persistent_liberality D M hM
      (gammaRestrict D M hM map) with
    ⟨universalMap, hUniversal, hUnique⟩
  have hLift : gammaLift D M hM (gammaRestrict D M hM map) =
      universalMap :=
    hUnique _ (gammaLift_agrees D M hM (gammaRestrict D M hM map))
  have hMap : map = universalMap := by
    apply hUnique
    intro s value
    rfl
  exact hLift.trans hMap.symm

/-- The adjunction-level content of persistent liberality, stated without
category-theory dependencies: maps `gamma D -> M` correspond exactly to
partial maps `D -> beta M`. -/
noncomputable def gammaBetaHomEquiv
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M) :
    HomEquiv (EncodedHom (gamma D) M) (PartialHom D (beta M hM)) where
  toFun := gammaRestrict D M hM
  invFun := gammaLift D M hM
  left_inv := gammaLift_gammaRestrict D M hM
  right_inv := gammaRestrict_gammaLift D M hM

/-! ## The induced `gamma` functor laws -/

/-- The action of `gamma` on partial-algebra homomorphisms, obtained from the
hom-set equivalence rather than defined ad hoc on normal forms. -/
noncomputable def gammaHom
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E) : EncodedHom (gamma D) (gamma E) :=
  gammaLift D (gamma E) (gamma_satisfiesGamma E)
    (PartialHom.comp (betaGammaHom E) hom)

theorem gammaRestrict_gammaHom
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E) :
    gammaRestrict D (gamma E) (gamma_satisfiesGamma E) (gammaHom hom) =
      PartialHom.comp (betaGammaHom E) hom :=
  gammaRestrict_gammaLift D (gamma E) (gamma_satisfiesGamma E)
    (PartialHom.comp (betaGammaHom E) hom)

theorem gammaHom_identity
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    gammaHom (PartialHom.identity D) = EncodedHom.identity (gamma D) := by
  change gammaLift D (gamma D) (gamma_satisfiesGamma D)
      (PartialHom.comp (betaGammaHom D) (PartialHom.identity D)) = _
  rw [PartialHom.comp_identity]
  have hRestrict :
      gammaRestrict D (gamma D) (gamma_satisfiesGamma D)
          (EncodedHom.identity (gamma D)) = betaGammaHom D := by
    apply PartialHom.ext
    funext s value
    apply Subtype.ext
    rfl
  rw [<- hRestrict]
  exact gammaLift_gammaRestrict D (gamma D) (gamma_satisfiesGamma D)
    (EncodedHom.identity (gamma D))

theorem gammaHom_comp
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    {F : PartialAlg.{u,x} Sigma}
    (g : PartialHom E F)
    (f : PartialHom D E) :
    gammaHom (PartialHom.comp g f) =
      EncodedHom.comp (gammaHom g) (gammaHom f) := by
  change gammaLift D (gamma F) (gamma_satisfiesGamma F)
      (PartialHom.comp (betaGammaHom F) (PartialHom.comp g f)) = _
  rw [<- gammaLift_gammaRestrict D (gamma F) (gamma_satisfiesGamma F)
    (EncodedHom.comp (gammaHom g) (gammaHom f))]
  congr 1

/-! ## The explicit Resolution normal-form presentation -/

/-- The data sorts of `gamma D` are precisely the generated Resolution normal
forms. This alias makes the bridge available without exposing the internal
truth-sort implementation. -/
abbrev ResolutionNormalForm
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) := Free.Generated D

theorem gamma_data_is_resolutionNormalForm
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    (gamma D).Data = ResolutionNormalForm D := rfl

/-- On old values, the functorial map induced by `gamma` is exactly the map of
the source partial homomorphism. -/
theorem gammaHom_generatedOld
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E)
    (s : Sigma.SortId)
    (value : D.Carrier s) :
    (gammaHom hom).dataMap s (Free.generatedOld D value) =
      Free.generatedOld E (hom.toFun s value) := by
  have hAgree := gammaLift_agrees D (gamma E) (gamma_satisfiesGamma E)
    (PartialHom.comp (betaGammaHom E) hom) s value
  exact congrArg Subtype.val hAgree

/-- `gamma` transports a generated total-operation normal form structurally.
-/
theorem gammaHom_generatedTotal
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E)
    (op : Sigma.TotalOp)
    (args : TotalArgs Sigma (Free.Generated D) op) :
    (gammaHom hom).dataMap _ (Free.generatedTotal D op args) =
      Free.generatedTotal E op
        (fun i => (gammaHom hom).dataMap _ (args i)) :=
  (gammaHom hom).map_total op args

/-- `gamma` transports a generated partial-symbol normal form structurally.
-/
theorem gammaHom_generatedPartial
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (hom : PartialHom D E)
    (op : Sigma.PartialOp)
    (args : PartialArgs Sigma (Free.Generated D) op) :
    (gammaHom hom).dataMap _ (Free.generatedPartial D op args) =
      Free.generatedPartial E op
        (fun i => (gammaHom hom).dataMap _ (args i)) :=
  (gammaHom hom).map_partial_symbol op args

/-! ## Satisfaction is invariant under partial-algebra equivalence -/

namespace PartialAlgEquiv

/-- The forward homomorphism carried by a partial-algebra equivalence. -/
def toHom
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E) : PartialHom D E where
  toFun := equiv.carrierEquiv.toFun
  map_total := by
    intro op args
    exact (equiv.map_total op args).symm
  map_partial := by
    intro op args result hEval
    rw [equiv.map_partial op args, hEval]
    rfl

/-- The inverse homomorphism carried by a partial-algebra equivalence. -/
def inverseHom
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E) : PartialHom E D where
  toFun := equiv.carrierEquiv.invFun
  map_total := by
    intro op args
    have hInjective : Function.Injective
        (equiv.carrierEquiv.toFun (Sigma.totalResultSort op)) := by
      intro left right hEqual
      calc
        left = equiv.carrierEquiv.invFun _
            (equiv.carrierEquiv.toFun _ left) :=
          (equiv.carrierEquiv.left_inv _ left).symm
        _ = equiv.carrierEquiv.invFun _
            (equiv.carrierEquiv.toFun _ right) :=
          congrArg (equiv.carrierEquiv.invFun _) hEqual
        _ = right := equiv.carrierEquiv.left_inv _ right
    apply hInjective
    have hArgs :
        (fun i => equiv.carrierEquiv.toFun _
          (equiv.carrierEquiv.invFun _ (args i))) = args := by
      funext i
      exact equiv.carrierEquiv.right_inv _ (args i)
    calc
      equiv.carrierEquiv.toFun _
          (equiv.carrierEquiv.invFun _ (E.evalTotal op args)) =
          E.evalTotal op args :=
        equiv.carrierEquiv.right_inv _ (E.evalTotal op args)
      _ = E.evalTotal op
          (fun i => equiv.carrierEquiv.toFun _
            (equiv.carrierEquiv.invFun _ (args i))) :=
        congrArg (E.evalTotal op) hArgs.symm
      _ = equiv.carrierEquiv.toFun _
          (D.evalTotal op
            (fun i => equiv.carrierEquiv.invFun _ (args i))) :=
        equiv.map_total op
          (fun i => equiv.carrierEquiv.invFun _ (args i))
  map_partial := by
    intro op args result hEval
    have hForward := equiv.map_partial op
      (fun i => equiv.carrierEquiv.invFun _ (args i))
    have hArgs :
        (fun i => equiv.carrierEquiv.toFun _
          (equiv.carrierEquiv.invFun _ (args i))) = args := by
      funext i
      exact equiv.carrierEquiv.right_inv _ (args i)
    rw [hArgs, hEval] at hForward
    cases hSource : D.evalPartial op
        (fun i => equiv.carrierEquiv.invFun _ (args i)) with
    | none => simp [hSource] at hForward
    | some sourceResult =>
        have hImage : equiv.carrierEquiv.toFun _ sourceResult = result := by
          have hForward' :
              result = equiv.carrierEquiv.toFun _ sourceResult := by
            simpa [hSource] using hForward
          exact hForward'.symm
        have hSourceResult : sourceResult =
            equiv.carrierEquiv.invFun _ result := by
          rw [<- hImage]
          exact (equiv.carrierEquiv.left_inv _ sourceResult).symm
        exact congrArg Option.some hSourceResult

end PartialAlgEquiv

namespace PartialHom

/-- Transport a variable assignment along a partial-algebra homomorphism. -/
def mapAssignment
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    (hom : PartialHom A B)
    {Var : Sigma.SortId -> Type x}
    (rho : Assignment Sigma Var A.Carrier) :
    Assignment Sigma Var B.Carrier :=
  fun s name => hom.toFun s (rho s name)

end PartialHom

/-- Defined term evaluation is preserved by every partial-algebra
homomorphism. This is the term-level engine used below to transport
satisfaction across an algebra equivalence. -/
theorem Term.evalPartial_map_some
    {Sigma : Signature.{u}}
    {A : PartialAlg.{u,v} Sigma}
    {B : PartialAlg.{u,w} Sigma}
    (hom : PartialHom A B)
    {Var : Sigma.SortId -> Type x}
    (rho : Assignment Sigma Var A.Carrier)
    {s : Sigma.SortId}
    (term : Term Sigma Var s)
    (result : A.Carrier s) :
    term.evalPartial A rho = some result ->
      term.evalPartial B (PartialHom.mapAssignment hom rho) =
        some (hom.toFun s result) := by
  induction term with
  | var name =>
      intro hEval
      change some (rho _ name) = some result at hEval
      change some (hom.toFun _ (rho _ name)) = some (hom.toFun _ result)
      exact congrArg (fun value => some (hom.toFun _ value))
        (Option.some.inj hEval)
  | total op args ih =>
      intro hEval
      let evaluatedA := fun i => Term.evalPartial A rho (args i)
      change (if h : AllSome evaluatedA then
          some (A.evalTotal op (fun i => someValue h i))
        else none) = some result at hEval
      by_cases hArgsA : AllSome evaluatedA
      · rw [dif_pos hArgsA] at hEval
        have hResult :
            A.evalTotal op (fun i => someValue hArgsA i) = result :=
          Option.some.inj hEval
        have hEach : forall i,
            Term.evalPartial B (PartialHom.mapAssignment hom rho) (args i) =
              some (hom.toFun _ (someValue hArgsA i)) := by
          intro i
          exact ih i (someValue hArgsA i) (someValue_spec hArgsA i)
        have hArgsB : AllSome
            (fun i => Term.evalPartial B
              (PartialHom.mapAssignment hom rho) (args i)) := by
          intro i
          exact ⟨hom.toFun _ (someValue hArgsA i), hEach i⟩
        change (if h : AllSome
            (fun i => Term.evalPartial B
              (PartialHom.mapAssignment hom rho) (args i)) then
            some (B.evalTotal op (fun i => someValue h i))
          else none) = some (hom.toFun _ result)
        rw [dif_pos hArgsB]
        congr 1
        have hSelected : forall i,
            someValue hArgsB i = hom.toFun _ (someValue hArgsA i) := by
          intro i
          have hSpec := someValue_spec hArgsB i
          rw [hEach i] at hSpec
          exact (Option.some.inj hSpec).symm
        calc
          B.evalTotal op (fun i => someValue hArgsB i) =
              B.evalTotal op
                (fun i => hom.toFun _ (someValue hArgsA i)) :=
            congrArg (B.evalTotal op) (funext hSelected)
          _ = hom.toFun _
              (A.evalTotal op (fun i => someValue hArgsA i)) :=
            (hom.map_total op (fun i => someValue hArgsA i)).symm
          _ = hom.toFun _ result := congrArg (hom.toFun _) hResult
      · rw [dif_neg hArgsA] at hEval
        cases hEval
  | partialApp op args ih =>
      intro hEval
      let evaluatedA := fun i => Term.evalPartial A rho (args i)
      change (if h : AllSome evaluatedA then
          A.evalPartial op (fun i => someValue h i)
        else none) = some result at hEval
      by_cases hArgsA : AllSome evaluatedA
      · rw [dif_pos hArgsA] at hEval
        have hEach : forall i,
            Term.evalPartial B (PartialHom.mapAssignment hom rho) (args i) =
              some (hom.toFun _ (someValue hArgsA i)) := by
          intro i
          exact ih i (someValue hArgsA i) (someValue_spec hArgsA i)
        have hArgsB : AllSome
            (fun i => Term.evalPartial B
              (PartialHom.mapAssignment hom rho) (args i)) := by
          intro i
          exact ⟨hom.toFun _ (someValue hArgsA i), hEach i⟩
        change (if h : AllSome
            (fun i => Term.evalPartial B
              (PartialHom.mapAssignment hom rho) (args i)) then
            B.evalPartial op (fun i => someValue h i)
          else none) = some (hom.toFun _ result)
        rw [dif_pos hArgsB]
        have hSelected : forall i,
            someValue hArgsB i = hom.toFun _ (someValue hArgsA i) := by
          intro i
          have hSpec := someValue_spec hArgsB i
          rw [hEach i] at hSpec
          exact (Option.some.inj hSpec).symm
        calc
          B.evalPartial op (fun i => someValue hArgsB i) =
              B.evalPartial op
                (fun i => hom.toFun _ (someValue hArgsA i)) :=
            congrArg (B.evalPartial op) (funext hSelected)
          _ = some (hom.toFun _ result) :=
            hom.map_partial op (fun i => someValue hArgsA i) result hEval
      · rw [dif_neg hArgsA] at hEval
        cases hEval

namespace PartialAlgEquiv

theorem inverse_mapAssignment
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E)
    {Var : Sigma.SortId -> Type x}
    (rho : Assignment Sigma Var D.Carrier) :
    PartialHom.mapAssignment (equiv.inverseHom)
        (PartialHom.mapAssignment equiv.toHom rho) = rho := by
  funext s name
  exact equiv.carrierEquiv.left_inv s (rho s name)

theorem mapAssignment_extend
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E)
    {context : List Sigma.SortId}
    (rho : ContextAssignment Sigma D.Carrier context)
    {s : Sigma.SortId}
    (value : D.Carrier s) :
    PartialHom.mapAssignment equiv.toHom
        (ContextAssignment.extend rho value) =
      ContextAssignment.extend
        (PartialHom.mapAssignment equiv.toHom rho)
        (equiv.carrierEquiv.toFun s value) := by
  funext t name
  cases name with
  | here => rfl
  | there name => rfl

theorem mapAssignment_extend_inverse
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E)
    {context : List Sigma.SortId}
    (rho : ContextAssignment Sigma D.Carrier context)
    {s : Sigma.SortId}
    (value : E.Carrier s) :
    PartialHom.mapAssignment equiv.toHom
        (ContextAssignment.extend rho
          (equiv.carrierEquiv.invFun s value)) =
      ContextAssignment.extend
        (PartialHom.mapAssignment equiv.toHom rho) value := by
  funext t name
  cases name with
  | here => exact equiv.carrierEquiv.right_inv s value
  | there name => rfl

end PartialAlgEquiv

/-- Tarskian satisfaction, including negation and total quantification, is
invariant under the repository's notion of partial-algebra equivalence. -/
theorem Formula.sat_iff_of_equiv
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E)
    {context : List Sigma.SortId}
    (rho : ContextAssignment Sigma D.Carrier context)
    (formula : Formula Sigma context) :
    formula.Sat D rho <->
      formula.Sat E (PartialHom.mapAssignment equiv.toHom rho) := by
  induction formula with
  | existenceEquality left right =>
      change
        (Exists fun value =>
          left.evalPartial D rho = some value /\
            right.evalPartial D rho = some value) <->
        (Exists fun value =>
          left.evalPartial E (PartialHom.mapAssignment equiv.toHom rho) =
              some value /\
            right.evalPartial E (PartialHom.mapAssignment equiv.toHom rho) =
              some value)
      constructor
      · rintro ⟨value, hLeft, hRight⟩
        exact ⟨equiv.carrierEquiv.toFun _ value,
          Term.evalPartial_map_some equiv.toHom rho left value hLeft,
          Term.evalPartial_map_some equiv.toHom rho right value hRight⟩
      · rintro ⟨value, hLeft, hRight⟩
        have hLeftBack := Term.evalPartial_map_some equiv.inverseHom
          (PartialHom.mapAssignment equiv.toHom rho) left value hLeft
        have hRightBack := Term.evalPartial_map_some equiv.inverseHom
          (PartialHom.mapAssignment equiv.toHom rho) right value hRight
        rw [equiv.inverse_mapAssignment rho] at hLeftBack hRightBack
        exact ⟨equiv.carrierEquiv.invFun _ value, hLeftBack, hRightBack⟩
  | conjunction left right ihLeft ihRight =>
      exact and_congr (ihLeft rho) (ihRight rho)
  | negation body ih =>
      exact not_congr (ih rho)
  | universal s body ih =>
      change
        (forall value : D.Carrier s,
          body.Sat D (ContextAssignment.extend rho value)) <->
        (forall value : E.Carrier s,
          body.Sat E
            (ContextAssignment.extend
              (PartialHom.mapAssignment equiv.toHom rho) value))
      constructor
      · intro h value
        have hMapped :=
          (ih (ContextAssignment.extend rho
            (equiv.carrierEquiv.invFun s value))).1
            (h (equiv.carrierEquiv.invFun s value))
        rw [equiv.mapAssignment_extend_inverse rho value] at hMapped
        exact hMapped
      · intro h value
        apply (ih (ContextAssignment.extend rho value)).2
        have hMapped := h (equiv.carrierEquiv.toFun s value)
        rw [equiv.mapAssignment_extend rho value]
        exact hMapped

/-! ## Semantic consequence, reflected and preserved by the encoding -/

/-- The unique assignment for the empty context. -/
def emptyContextAssignment
    {Sigma : Signature.{u}}
    (Carrier : Sigma.SortId -> Type v) :
    ContextAssignment Sigma Carrier [] :=
  fun _ name => nomatch name

/-- Satisfaction of a closed partial-algebra formula. -/
def Formula.Holds
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (formula : Formula Sigma []) : Prop :=
  formula.Sat D (emptyContextAssignment D.Carrier)

/-- Satisfaction of a closed encoded formula. -/
def EncodedFormula.Holds
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (formula : EncodedFormula Sigma []) : Prop :=
  formula.Sat M (emptyContextAssignment M.Data)

theorem Formula.holds_iff_of_equiv
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (equiv : PartialAlgEquiv D E)
    (formula : Formula Sigma []) :
    formula.Holds D <-> formula.Holds E := by
  have hSat := Formula.sat_iff_of_equiv equiv
    (emptyContextAssignment D.Carrier) formula
  have hEmpty :
      PartialHom.mapAssignment equiv.toHom
          (emptyContextAssignment D.Carrier) =
        emptyContextAssignment E.Carrier := by
    funext s name
    cases name
  rw [hEmpty] at hSat
  exact hSat

theorem alpha_holds_iff
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (formula : Formula Sigma []) :
    formula.Holds (beta M hM) <-> (alpha formula).Holds M := by
  have hSat := alpha_satisfaction_condition M hM
    (emptyContextAssignment (beta M hM).Carrier) formula
  have hEmpty :
      liftBetaAssignment hM
          (emptyContextAssignment (beta M hM).Carrier) =
        emptyContextAssignment M.Data := by
    funext s name
    cases name
  rw [hEmpty] at hSat
  exact hSat

abbrev PartialTheory
    (Sigma : Signature.{u}) := Formula Sigma [] -> Prop

def ModelsPartialTheory
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (theory : PartialTheory Sigma) : Prop :=
  forall formula, theory formula -> formula.Holds D

/-- Models of `Gamma` satisfying the `alpha`-translation of a partial theory.
-/
def ModelsEncodedTranslation
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (theory : PartialTheory Sigma) : Prop :=
  forall formula, theory formula -> (alpha formula).Holds M

/-- Universe-bounded semantic consequence for partial algebras. The carrier
level is closed under the `gamma` construction by taking `max u v`. -/
def PartialSemanticConsequence
    {Sigma : Signature.{u}}
    (premises conclusions : PartialTheory Sigma) : Prop :=
  forall D : PartialAlg.{u,max u v} Sigma,
    ModelsPartialTheory D premises -> ModelsPartialTheory D conclusions

/-- Semantic consequence after translation, relative to encoded models of
`Gamma`. -/
def EncodedSemanticConsequence
    {Sigma : Signature.{u}}
    (premises conclusions : PartialTheory Sigma) : Prop :=
  forall M : EncodedAlg.{u,max u v,max u v} Sigma,
    SatisfiesGamma M ->
      ModelsEncodedTranslation M premises ->
        ModelsEncodedTranslation M conclusions

/-- Diaconescu's semantic consequence equivalence (Corollary 4.3), checked
for arbitrary theories of closed formulas. The reverse implication uses the
canonical `gamma` model and satisfaction invariance under
`betaGammaPartialAlgEquiv`; no definitional equality is assumed. -/
theorem semantic_consequence_equivalence
    {Sigma : Signature.{u}}
    (premises conclusions : PartialTheory Sigma) :
    PartialSemanticConsequence.{u,v} premises conclusions <->
      EncodedSemanticConsequence.{u,v} premises conclusions := by
  constructor
  · intro hPartial M hM hPremises formula hFormula
    apply (alpha_holds_iff M hM formula).1
    apply hPartial (beta M hM)
    · intro premise hPremise
      exact (alpha_holds_iff M hM premise).2
        (hPremises premise hPremise)
    · exact hFormula
  · intro hEncoded D hPremises formula hFormula
    let gammaModel := gamma D
    have hGamma : SatisfiesGamma gammaModel := gamma_satisfiesGamma D
    have hTranslatedPremises :
        ModelsEncodedTranslation gammaModel premises := by
      intro premise hPremise
      apply (alpha_holds_iff gammaModel hGamma premise).1
      exact (Formula.holds_iff_of_equiv
        (betaGammaPartialAlgEquiv D) premise).1
          (hPremises premise hPremise)
    have hTranslatedConclusion :=
      hEncoded gammaModel hGamma hTranslatedPremises formula hFormula
    apply (Formula.holds_iff_of_equiv
      (betaGammaPartialAlgEquiv D) formula).2
    exact (alpha_holds_iff gammaModel hGamma formula).2
      hTranslatedConclusion

end ManySorted
end Diaconescu
end Resolution
