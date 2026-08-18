import ResolutionDiaconescuContinuation

universe u v w x y z q

namespace Resolution
namespace Diaconescu
namespace ManySorted

/-!
# The concrete `gamma ⊣ beta` adjunction and initial-model transfer

This module closes the category-level algebra that can be stated without an
external category-theory dependency.  The hom-set equivalence from
`ResolutionDiaconescuContinuation` is proved natural in both variables, its
unit and counit satisfy the triangle identities, and the resulting left
adjoint transports universe-bounded initial models of a fixed-signature theory
to initial models of its encoded translation.  Conversely, when the encoded
translation has an initial model, its `beta` reduct is proved initial on the
partial side; this is the categorical transfer used in Corollary 4.2.

The final theorem is deliberately narrower than an institution-theoretic
initial-semantics theorem: signatures are fixed, theories contain closed
formulas in the repository's concrete syntax, and no claim about arbitrary
signature morphisms is made.
-/

namespace EncodedHom

theorem comp_assoc
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    {P : EncodedAlg.{u,z,q} Sigma}
    {Q : EncodedAlg.{u,v,x} Sigma}
    (h : EncodedHom P Q)
    (g : EncodedHom N P)
    (f : EncodedHom M N) :
    comp h (comp g f) = comp (comp h g) f := by
  apply EncodedHom.ext
  · rfl
  · rfl

end EncodedHom

/-! ## Naturality of the hom-set equivalence -/

/-- Restriction along `gamma ⊣ beta` is natural in the encoded target. -/
theorem gammaRestrict_natural_target
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    {M : EncodedAlg.{u,w,x} Sigma}
    {N : EncodedAlg.{u,y,z} Sigma}
    (hM : SatisfiesGamma M)
    (hN : SatisfiesGamma N)
    (map : EncodedHom M N)
    (source : EncodedHom (gamma D) M) :
    gammaRestrict D N hN (EncodedHom.comp map source) =
      PartialHom.comp (betaHom hM hN map)
        (gammaRestrict D M hM source) := by
  apply PartialHom.ext
  funext s value
  apply Subtype.ext
  rfl

/-- Restriction along `gamma ⊣ beta` is natural in the partial source. -/
theorem gammaRestrict_natural_source
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (map : PartialHom D E)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (target : EncodedHom (gamma E) M) :
    gammaRestrict D M hM
        (EncodedHom.comp target (gammaHom map)) =
      PartialHom.comp (gammaRestrict E M hM target) map := by
  apply PartialHom.ext
  funext s value
  apply Subtype.ext
  exact congrArg (target.dataMap s)
    (gammaHom_generatedOld map s value)

/-- The inverse hom-set map is natural in the encoded target. -/
theorem gammaLift_natural_target
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    {M : EncodedAlg.{u,w,x} Sigma}
    {N : EncodedAlg.{u,y,z} Sigma}
    (hM : SatisfiesGamma M)
    (hN : SatisfiesGamma N)
    (map : EncodedHom M N)
    (source : PartialHom D (beta M hM)) :
    EncodedHom.comp map (gammaLift D M hM source) =
      gammaLift D N hN
        (PartialHom.comp (betaHom hM hN map) source) := by
  calc
    EncodedHom.comp map (gammaLift D M hM source) =
        gammaLift D N hN
          (gammaRestrict D N hN
            (EncodedHom.comp map (gammaLift D M hM source))) :=
      (gammaLift_gammaRestrict D N hN
        (EncodedHom.comp map (gammaLift D M hM source))).symm
    _ = gammaLift D N hN
        (PartialHom.comp (betaHom hM hN map) source) := by
      congr 1

/-- The inverse hom-set map is natural in the partial source. -/
theorem gammaLift_natural_source
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (map : PartialHom D E)
    (M : EncodedAlg.{u,x,y} Sigma)
    (hM : SatisfiesGamma M)
    (target : PartialHom E (beta M hM)) :
    EncodedHom.comp (gammaLift E M hM target) (gammaHom map) =
      gammaLift D M hM (PartialHom.comp target map) := by
  calc
    EncodedHom.comp (gammaLift E M hM target) (gammaHom map) =
        gammaLift D M hM
          (gammaRestrict D M hM
            (EncodedHom.comp (gammaLift E M hM target)
              (gammaHom map))) :=
      (gammaLift_gammaRestrict D M hM
        (EncodedHom.comp (gammaLift E M hM target)
          (gammaHom map))).symm
    _ = gammaLift D M hM (PartialHom.comp target map) := by
      congr 1

/-! ## Unit, counit, and triangle identities -/

theorem gammaRestrict_identity
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    gammaRestrict D (gamma D) (gamma_satisfiesGamma D)
        (EncodedHom.identity (gamma D)) =
      betaGammaHom D := by
  apply PartialHom.ext
  funext s value
  apply Subtype.ext
  rfl

/-- Naturality of the unit `D -> beta (gamma D)`. -/
theorem betaGammaHom_natural
    {Sigma : Signature.{u}}
    {D : PartialAlg.{u,v} Sigma}
    {E : PartialAlg.{u,w} Sigma}
    (map : PartialHom D E) :
    PartialHom.comp
        (betaHom (gamma_satisfiesGamma D) (gamma_satisfiesGamma E)
          (gammaHom map))
        (betaGammaHom D) =
      PartialHom.comp (betaGammaHom E) map := by
  change gammaRestrict D (gamma E) (gamma_satisfiesGamma E)
      (gammaHom map) = _
  exact gammaRestrict_gammaHom map

/-- The counit `gamma (beta M) -> M`, obtained from the identity of the
`beta` reduct under the hom-set equivalence. -/
noncomputable def gammaBetaCounit
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M) :
    EncodedHom (gamma (beta M hM)) M :=
  gammaLift (beta M hM) M hM (PartialHom.identity (beta M hM))

theorem gammaRestrict_counit
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M) :
    gammaRestrict (beta M hM) M hM (gammaBetaCounit M hM) =
      PartialHom.identity (beta M hM) := by
  exact gammaRestrict_gammaLift (beta M hM) M hM
    (PartialHom.identity (beta M hM))

/-- Naturality of the counit `gamma (beta M) -> M`. -/
theorem gammaBetaCounit_natural
    {Sigma : Signature.{u}}
    {M : EncodedAlg.{u,v,w} Sigma}
    {N : EncodedAlg.{u,x,y} Sigma}
    (hM : SatisfiesGamma M)
    (hN : SatisfiesGamma N)
    (map : EncodedHom M N) :
    EncodedHom.comp map (gammaBetaCounit M hM) =
      EncodedHom.comp (gammaBetaCounit N hN)
        (gammaHom (betaHom hM hN map)) := by
  calc
    EncodedHom.comp map (gammaBetaCounit M hM) =
        gammaLift (beta M hM) N hN
          (PartialHom.comp (betaHom hM hN map)
            (PartialHom.identity (beta M hM))) :=
      gammaLift_natural_target (beta M hM) hM hN map
        (PartialHom.identity (beta M hM))
    _ = gammaLift (beta M hM) N hN (betaHom hM hN map) := by
      rw [PartialHom.comp_identity]
    _ = EncodedHom.comp (gammaBetaCounit N hN)
        (gammaHom (betaHom hM hN map)) := by
      symm
      calc
        EncodedHom.comp (gammaBetaCounit N hN)
            (gammaHom (betaHom hM hN map)) =
          gammaLift (beta M hM) N hN
            (PartialHom.comp (PartialHom.identity (beta N hN))
              (betaHom hM hN map)) :=
          gammaLift_natural_source (betaHom hM hN map) N hN
            (PartialHom.identity (beta N hN))
        _ = gammaLift (beta M hM) N hN (betaHom hM hN map) := by
          rw [PartialHom.identity_comp]

/-- The triangle identity on the `beta` side. -/
theorem gammaBeta_triangle_beta
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M) :
    PartialHom.comp
        (betaHom (gamma_satisfiesGamma (beta M hM)) hM
          (gammaBetaCounit M hM))
        (betaGammaHom (beta M hM)) =
      PartialHom.identity (beta M hM) := by
  change gammaRestrict (beta M hM) M hM
      (gammaBetaCounit M hM) = _
  exact gammaRestrict_counit M hM

/-- The triangle identity on the `gamma` side. -/
theorem gammaBeta_triangle_gamma
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    EncodedHom.comp
        (gammaBetaCounit (gamma D) (gamma_satisfiesGamma D))
        (gammaHom (betaGammaHom D)) =
      EncodedHom.identity (gamma D) := by
  calc
    EncodedHom.comp
        (gammaBetaCounit (gamma D) (gamma_satisfiesGamma D))
        (gammaHom (betaGammaHom D)) =
      gammaLift D (gamma D) (gamma_satisfiesGamma D)
        (PartialHom.comp
          (PartialHom.identity
            (beta (gamma D) (gamma_satisfiesGamma D)))
          (betaGammaHom D)) :=
      gammaLift_natural_source (betaGammaHom D) (gamma D)
        (gamma_satisfiesGamma D)
        (PartialHom.identity
          (beta (gamma D) (gamma_satisfiesGamma D)))
    _ = gammaLift D (gamma D) (gamma_satisfiesGamma D)
        (betaGammaHom D) := by
      rw [PartialHom.identity_comp]
    _ = gammaLift D (gamma D) (gamma_satisfiesGamma D)
        (gammaRestrict D (gamma D) (gamma_satisfiesGamma D)
          (EncodedHom.identity (gamma D))) := by
      rw [gammaRestrict_identity]
    _ = EncodedHom.identity (gamma D) :=
      gammaLift_gammaRestrict D (gamma D) (gamma_satisfiesGamma D)
        (EncodedHom.identity (gamma D))

/-! ## The canonical inverse to the unit -/

/-- The inverse homomorphism carried by the canonical equivalence
`D ~= beta (gamma D)`. -/
noncomputable def betaGammaInverseHom
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    PartialHom (beta (gamma D) (gamma_satisfiesGamma D)) D :=
  (betaGammaPartialAlgEquiv D).inverseHom

theorem betaGammaInverseHom_comp_betaGammaHom
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    PartialHom.comp (betaGammaInverseHom D) (betaGammaHom D) =
      PartialHom.identity D := by
  apply PartialHom.ext
  funext s value
  exact (betaGammaPartialAlgEquiv D).carrierEquiv.left_inv s value

theorem betaGammaHom_comp_betaGammaInverseHom
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma) :
    PartialHom.comp (betaGammaHom D) (betaGammaInverseHom D) =
      PartialHom.identity
        (beta (gamma D) (gamma_satisfiesGamma D)) := by
  apply PartialHom.ext
  funext s value
  exact (betaGammaPartialAlgEquiv D).carrierEquiv.right_inv s value

/-- Applying `beta` to the counit gives exactly the canonical inverse of the
unit, not merely an unspecified left inverse. -/
theorem betaHom_counit_eq_betaGammaInverseHom
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M) :
    betaHom (gamma_satisfiesGamma (beta M hM)) hM
        (gammaBetaCounit M hM) =
      betaGammaInverseHom (beta M hM) := by
  apply PartialHom.ext
  funext s value
  rcases betaGammaEmbed_surjective (beta M hM) s value with
    ⟨source, rfl⟩
  have hTriangle := congrArg
    (fun map => map.toFun s source)
    (gammaBeta_triangle_beta M hM)
  change
    (betaHom (gamma_satisfiesGamma (beta M hM)) hM
      (gammaBetaCounit M hM)).toFun s
        ((betaGammaHom (beta M hM)).toFun s source) =
      (betaGammaInverseHom (beta M hM)).toFun s
        ((betaGammaHom (beta M hM)).toFun s source)
  calc
    (betaHom (gamma_satisfiesGamma (beta M hM)) hM
        (gammaBetaCounit M hM)).toFun s
          ((betaGammaHom (beta M hM)).toFun s source) = source := by
      simpa using hTriangle
    _ = (betaGammaInverseHom (beta M hM)).toFun s
        ((betaGammaHom (beta M hM)).toFun s source) :=
      ((betaGammaPartialAlgEquiv (beta M hM)).carrierEquiv.left_inv
        s source).symm

/-- Any section of the counit becomes the unit after applying `beta`.  This
is the algebraic cancellation step used in the initial-model argument. -/
theorem betaHom_section_eq_betaGammaHom
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (unitSection : EncodedHom M (gamma (beta M hM)))
    (hSection :
      EncodedHom.comp (gammaBetaCounit M hM) unitSection =
        EncodedHom.identity M) :
    betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection =
      betaGammaHom (beta M hM) := by
  have hMapped := congrArg (betaHom hM hM) hSection
  rw [betaHom_comp hM (gamma_satisfiesGamma (beta M hM)) hM
      (gammaBetaCounit M hM) unitSection,
    betaHom_identity,
    betaHom_counit_eq_betaGammaInverseHom] at hMapped
  calc
    betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection =
        PartialHom.comp
          (PartialHom.identity
            (beta (gamma (beta M hM))
              (gamma_satisfiesGamma (beta M hM))))
          (betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection) :=
      (PartialHom.identity_comp _).symm
    _ = PartialHom.comp
        (PartialHom.comp (betaGammaHom (beta M hM))
          (betaGammaInverseHom (beta M hM)))
        (betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection) := by
      rw [betaGammaHom_comp_betaGammaInverseHom]
    _ = PartialHom.comp (betaGammaHom (beta M hM))
        (PartialHom.comp (betaGammaInverseHom (beta M hM))
          (betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection)) :=
      (PartialHom.comp_assoc _ _ _).symm
    _ = PartialHom.comp (betaGammaHom (beta M hM))
        (PartialHom.identity (beta M hM)) := by
      rw [hMapped]
    _ = betaGammaHom (beta M hM) :=
      PartialHom.comp_identity _

/-! ## Fixed-signature initial models -/

/-- Universe-bounded initiality among partial models of a fixed theory.  The
carrier universe `max u v` is closed under the canonical `gamma` construction.
-/
structure IsInitialPartialModel
    {Sigma : Signature.{u}}
    (theory : PartialTheory Sigma)
    (D : PartialAlg.{u,max u v} Sigma) : Prop where
  models : ModelsPartialTheory D theory
  hom_unique : forall E : PartialAlg.{u,max u v} Sigma,
    ModelsPartialTheory E theory ->
      Exists fun initialMap : PartialHom D E =>
        forall candidate : PartialHom D E, candidate = initialMap

/-- Universe-bounded initiality among encoded models of `Gamma` and the
`alpha`-translation of a fixed partial theory. -/
structure IsInitialEncodedModel
    {Sigma : Signature.{u}}
    (theory : PartialTheory Sigma)
    (M : EncodedAlg.{u,max u v,max u v} Sigma) : Prop where
  satisfiesGamma : SatisfiesGamma M
  models : ModelsEncodedTranslation M theory
  hom_unique : forall N : EncodedAlg.{u,max u v,max u v} Sigma,
    SatisfiesGamma N ->
      ModelsEncodedTranslation N theory ->
        Exists fun initialMap : EncodedHom M N =>
          forall candidate : EncodedHom M N, candidate = initialMap

theorem beta_models_partial_iff_encoded_translation
    {Sigma : Signature.{u}}
    (M : EncodedAlg.{u,v,w} Sigma)
    (hM : SatisfiesGamma M)
    (theory : PartialTheory Sigma) :
    ModelsPartialTheory (beta M hM) theory <->
      ModelsEncodedTranslation M theory := by
  constructor
  · intro hModels formula hFormula
    exact (alpha_holds_iff M hM formula).1
      (hModels formula hFormula)
  · intro hModels formula hFormula
    exact (alpha_holds_iff M hM formula).2
      (hModels formula hFormula)

theorem gamma_models_translation_iff_partial
    {Sigma : Signature.{u}}
    (D : PartialAlg.{u,v} Sigma)
    (theory : PartialTheory Sigma) :
    ModelsEncodedTranslation (gamma D) theory <->
      ModelsPartialTheory D theory := by
  constructor
  · intro hModels formula hFormula
    apply (Formula.holds_iff_of_equiv
      (betaGammaPartialAlgEquiv D) formula).2
    exact (alpha_holds_iff (gamma D) (gamma_satisfiesGamma D)
      formula).2 (hModels formula hFormula)
  · intro hModels formula hFormula
    apply (alpha_holds_iff (gamma D) (gamma_satisfiesGamma D)
      formula).1
    exact (Formula.holds_iff_of_equiv
      (betaGammaPartialAlgEquiv D) formula).1
        (hModels formula hFormula)

/-- Fixed-signature initial-model transfer: the concrete left adjoint `gamma`
sends an initial partial model of a theory to an initial encoded model of
`Gamma` together with its `alpha`-translation.  This is the operations-only,
universe-bounded core of the initial-model consequence of persistent
liberality; it does not quantify over signature morphisms or institution
presentations. -/
theorem gamma_preserves_initiality
    {Sigma : Signature.{u}}
    (theory : PartialTheory Sigma)
    (D : PartialAlg.{u,max u v} Sigma)
    (hInitial : IsInitialPartialModel.{u,v} theory D) :
    IsInitialEncodedModel.{u,v} theory (gamma D) := by
  refine
    { satisfiesGamma := gamma_satisfiesGamma D
      models := (gamma_models_translation_iff_partial D theory).2
        hInitial.models
      hom_unique := ?_ }
  intro M hM hModels
  have hBetaModels : ModelsPartialTheory (beta M hM) theory :=
    (beta_models_partial_iff_encoded_translation M hM theory).2 hModels
  rcases hInitial.hom_unique (beta M hM) hBetaModels with
    ⟨initialMap, hUnique⟩
  refine ⟨gammaLift D M hM initialMap, ?_⟩
  intro candidate
  have hRestrict : gammaRestrict D M hM candidate = initialMap :=
    hUnique (gammaRestrict D M hM candidate)
  calc
    candidate = gammaLift D M hM
        (gammaRestrict D M hM candidate) :=
      (gammaLift_gammaRestrict D M hM candidate).symm
    _ = gammaLift D M hM initialMap :=
      congrArg (gammaLift D M hM) hRestrict

/-- The transfer direction used in Diaconescu's Corollary 4.2: if the encoded
theory `Gamma + alpha(E)` has an initial total model `M`, then `beta M` is an
initial partial model of `E`.  The theorem isolates the categorical transfer;
existence of the encoded initial model for conditional-equational theories is
a separate classical algebra result. -/
theorem beta_of_initial_encoded_is_initial
    {Sigma : Signature.{u}}
    (theory : PartialTheory Sigma)
    (M : EncodedAlg.{u,max u v,max u v} Sigma)
    (hInitial : IsInitialEncodedModel.{u,v} theory M) :
    IsInitialPartialModel.{u,v} theory
      (beta M hInitial.satisfiesGamma) := by
  let hM := hInitial.satisfiesGamma
  have hBetaModels : ModelsPartialTheory (beta M hM) theory :=
    (beta_models_partial_iff_encoded_translation M hM theory).2
      hInitial.models
  have hGammaBetaModels :
      ModelsEncodedTranslation (gamma (beta M hM)) theory :=
    (gamma_models_translation_iff_partial (beta M hM) theory).2
      hBetaModels
  rcases hInitial.hom_unique (gamma (beta M hM))
      (gamma_satisfiesGamma (beta M hM)) hGammaBetaModels with
    ⟨unitSection, hSectionUnique⟩
  rcases hInitial.hom_unique M hM hInitial.models with
    ⟨initialEndomorphism, hEndomorphismUnique⟩
  have hSection :
      EncodedHom.comp (gammaBetaCounit M hM) unitSection =
        EncodedHom.identity M :=
    (hEndomorphismUnique
      (EncodedHom.comp (gammaBetaCounit M hM) unitSection)).trans
        (hEndomorphismUnique (EncodedHom.identity M)).symm
  have hBetaSection :
      betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection =
        betaGammaHom (beta M hM) :=
    betaHom_section_eq_betaGammaHom M hM unitSection hSection
  refine
    { models := hBetaModels
      hom_unique := ?_ }
  intro D hDModels
  have hGammaDModels : ModelsEncodedTranslation (gamma D) theory :=
    (gamma_models_translation_iff_partial D theory).2 hDModels
  rcases hInitial.hom_unique (gamma D) (gamma_satisfiesGamma D)
      hGammaDModels with ⟨encodedInitialMap, hEncodedUnique⟩
  let partialInitialMap : PartialHom (beta M hM) D :=
    PartialHom.comp (betaGammaInverseHom D)
      (betaHom hM (gamma_satisfiesGamma D) encodedInitialMap)
  refine ⟨partialInitialMap, ?_⟩
  intro candidate
  have hEncoded :
      EncodedHom.comp (gammaHom candidate) unitSection = encodedInitialMap :=
    hEncodedUnique (EncodedHom.comp (gammaHom candidate) unitSection)
  have hUnitCandidate :
      PartialHom.comp (betaGammaHom D) candidate =
        betaHom hM (gamma_satisfiesGamma D) encodedInitialMap := by
    calc
      PartialHom.comp (betaGammaHom D) candidate =
          PartialHom.comp
            (betaHom (gamma_satisfiesGamma (beta M hM))
              (gamma_satisfiesGamma D) (gammaHom candidate))
            (betaGammaHom (beta M hM)) :=
        (betaGammaHom_natural candidate).symm
      _ = PartialHom.comp
          (betaHom (gamma_satisfiesGamma (beta M hM))
            (gamma_satisfiesGamma D) (gammaHom candidate))
          (betaHom hM (gamma_satisfiesGamma (beta M hM)) unitSection) := by
        rw [hBetaSection]
      _ = betaHom hM (gamma_satisfiesGamma D)
          (EncodedHom.comp (gammaHom candidate) unitSection) :=
        (betaHom_comp hM (gamma_satisfiesGamma (beta M hM))
          (gamma_satisfiesGamma D) (gammaHom candidate) unitSection).symm
      _ = betaHom hM (gamma_satisfiesGamma D) encodedInitialMap :=
        congrArg (betaHom hM (gamma_satisfiesGamma D)) hEncoded
  change candidate = partialInitialMap
  calc
    candidate = PartialHom.comp (PartialHom.identity D) candidate :=
      (PartialHom.identity_comp candidate).symm
    _ = PartialHom.comp
        (PartialHom.comp (betaGammaInverseHom D) (betaGammaHom D))
        candidate := by
      rw [betaGammaInverseHom_comp_betaGammaHom]
    _ = PartialHom.comp (betaGammaInverseHom D)
        (PartialHom.comp (betaGammaHom D) candidate) :=
      (PartialHom.comp_assoc _ _ _).symm
    _ = PartialHom.comp (betaGammaInverseHom D)
        (betaHom hM (gamma_satisfiesGamma D) encodedInitialMap) :=
      congrArg (PartialHom.comp (betaGammaInverseHom D)) hUnitCandidate
    _ = partialInitialMap := rfl

/-- Existence-level form of the same transfer: an initial encoded model yields
an initial partial model in the same universe bound. -/
theorem initial_partial_exists_of_encoded_initial_exists
    {Sigma : Signature.{u}}
    (theory : PartialTheory Sigma)
    (hExists : Exists fun M : EncodedAlg.{u,max u v,max u v} Sigma =>
      IsInitialEncodedModel.{u,v} theory M) :
    Exists fun D : PartialAlg.{u,max u v} Sigma =>
      IsInitialPartialModel.{u,v} theory D := by
  rcases hExists with ⟨M, hInitial⟩
  exact ⟨beta M hInitial.satisfiesGamma,
    beta_of_initial_encoded_is_initial theory M hInitial⟩

end ManySorted
end Diaconescu
end Resolution
