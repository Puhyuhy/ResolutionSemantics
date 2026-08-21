import ResolutionStrongTotalityMinimality
import ResolutionStrongTotalityNormalForm
import ResolutionStrongTotalityUniversalNaturality
import ResolutionStrongTotalityRepresentationInvariant
import ResolutionStrongTotalityDependent
import ResolutionStrongTotalitySingletonFamily
import ResolutionStrongTotalityFamilyConjugation
import ResolutionStrongTotalityFamilyResidualCoherence
import ResolutionStrongTotalityNoGo
import ResolutionStrongTotalityKernelBridge
import ResolutionStrongTotalityWellFormed

/-!
# Grand characterization of Strong Totality

This module collects the foundational Strong Totality theory into one
propositional package.  The point is not to introduce a stronger axiom, but to
state in one place exactly what the canonical Resolution completion has already
been proved to be.

For a well-formed specification `S`, `ResolutionAnswer S` is simultaneously:

* total, even when `S` has no ordinary solution;
* the free pointed extension of the ordinary solution space;
* exactly `Solution S + 1`, with no hidden semantic states;
* exact with respect to ordinary satisfiability;
* uniquely canonical among universal pointed completions;
* functorial and universally natural under specification morphisms.

The same structure extends coherently to dependent families, reindexing, and
fiberwise residual-provenance vocabularies.  The package also records the exact
external domain of the principle for raw syntax, the classical boundary for
proof-carrying impossibility residuals, the no-go theorem forbidding collapse
back to ordinary solvability, and the lossless bridge to the pre-existing
Resolution kernel.
-/

universe u r v w z

namespace Resolution
namespace StrongTotality

/-- One specification together with the global coherence properties that make
its Resolution completion part of the full Strong Totality theory. -/
structure StrongTotalityGrandCharacterization
    (S : Specification.{u}) : Prop where
  /-- Every well-formed specification has a Resolution Answer. -/
  total : Nonempty (ResolutionAnswer S)

  /-- The canonical answer space is the free pointed completion of ordinary
  solutions. -/
  freePointed :
    IsUniversalTotalization S (ResolutionAnswer S)
      (@realizeSolution S)
      (ResolutionAnswer.residual : ResolutionAnswer S)

  /-- Ordinary satisfiability is exactly the existence of a non-residual
  Resolution Answer. -/
  exact :
    Specification.Satisfiable S ↔
      Exists fun a : ResolutionAnswer S =>
        a ≠ (ResolutionAnswer.residual : ResolutionAnswer S)

  /-- The minimal completion literally adds one point. -/
  normalForm :
    Nonempty
      (Equiv (ResolutionAnswer S)
        (Sum (Specification.Solution S) Unit))

  /-- Every universal presentation has exactly the forced state-space shape. -/
  rigidUniversal :
    forall (X : Type u)
      (includeSolution : Specification.Solution S -> X)
      (residual : X),
      IsUniversalTotalization S X includeSolution residual ->
        Function.Injective includeSolution ∧
          (forall x : Specification.Solution S,
            includeSolution x ≠ residual) ∧
          (forall q : X,
            (Exists fun x : Specification.Solution S =>
              q = includeSolution x) ∨ q = residual)

  /-- Every universal presentation has one unique structural equivalence to the
  canonical Resolution completion. -/
  uniqueCanonical :
    forall (X : Type u)
      (includeSolution : Specification.Solution S -> X)
      (residual : X)
      (hX : IsUniversalTotalization S X includeSolution residual),
      Exists fun e : Equiv X (ResolutionAnswer S) =>
        ((forall x : Specification.Solution S,
            e (includeSolution x) = realizeSolution x) ∧
          e residual =
            (ResolutionAnswer.residual : ResolutionAnswer S)) ∧
        forall g : Equiv X (ResolutionAnswer S),
          ((forall x : Specification.Solution S,
              g (includeSolution x) = realizeSolution x) ∧
            g residual =
              (ResolutionAnswer.residual : ResolutionAnswer S)) ->
          g = e

  /-- Resolution transport respects identity specification translations. -/
  functorIdentity :
    forall a : ResolutionAnswer S,
      ResolutionAnswer.map (SpecMorphism.id S) a = a

  /-- Resolution transport respects composition. -/
  functorComposition :
    forall {T U : Specification.{u}}
      (g : SpecMorphism T U)
      (f : SpecMorphism S T)
      (a : ResolutionAnswer S),
      ResolutionAnswer.map (SpecMorphism.comp g f) a =
        ResolutionAnswer.map g (ResolutionAnswer.map f a)

  /-- The functorial action is exactly the unique action forced by relative
  initiality. -/
  universalNaturality :
    forall {T : Specification.{u}}
      (f : SpecMorphism S T),
      Exists fun p : CompletionHomOver f
          (canonicalCompletion S) (canonicalCompletion T) =>
        forall q : CompletionHomOver f
            (canonicalCompletion S) (canonicalCompletion T),
          q = p

  /-- Equivalent presentations induce equivalent Resolution spaces. -/
  representationInvariant :
    forall {T : Specification.{u}}
      (e : SpecEquiv S T),
      Nonempty (Equiv (ResolutionAnswer S) (ResolutionAnswer T))

  /-- Strong Totality is closed under genuinely dependent specifications. -/
  dependentClosure :
    forall T : Specification.Solution S -> Specification.{u},
      Nonempty (ResolutionAnswer (dependentSpecification S T))

  /-- The one-specification universal property is exactly the singleton-family
  instance of family universality. -/
  singletonFamily :
    forall (X : Type u)
      (includeSolution : Specification.Solution S -> X)
      (residual : X),
      IsUniversalTotalization S X includeSolution residual ↔
        IsUniversalTotalizationFamily
          (singletonSpecificationFamily S)
          (fun _ : Unit => X)
          (fun _ => includeSolution)
          (fun _ => residual)

  /-- Canonical Strong Totality is simultaneous over arbitrary dependent
  families of specifications. -/
  familyUniversal :
    forall {I : Type v}
      (F : I -> Specification.{u}),
      IsUniversalTotalizationFamily F
        (fun i => ResolutionAnswer (F i))
        (fun i => @realizeSolution (F i))
        (fun i =>
          (ResolutionAnswer.residual : ResolutionAnswer (F i)))

  /-- Family universality is exactly unique structural canonicity. -/
  familyClassification :
    forall {I : Type v}
      (F : I -> Specification.{u})
      (A : FamilyCompletionObject F),
      IsUniversalFamilyCompletion F A ↔
        Exists fun e : (i : I) ->
            Equiv (A.Carrier i) (ResolutionAnswer (F i)) =>
          IsCanonicalFamilyEquiv F A e ∧
          forall g : (i : I) ->
              Equiv (A.Carrier i) (ResolutionAnswer (F i)),
            IsCanonicalFamilyEquiv F A g -> g = e

  /-- Canonical family transport preserves identities. -/
  familyFunctorIdentity :
    forall {I : Type v}
      (F : I -> Specification.{u}),
      canonicalFamilyCompletionMap (FamilySpecMorphism.id F) =
        FamilyCompletionHomOver.id (canonicalFamilyCompletion F)

  /-- Canonical family transport preserves composition, including reindexing. -/
  familyFunctorComposition :
    forall {I : Type v}
      {J : Type w}
      {K : Type z}
      {F : I -> Specification.{u}}
      {G : J -> Specification.{u}}
      {H : K -> Specification.{u}}
      (eta : FamilySpecMorphism F G)
      (theta : FamilySpecMorphism G H),
      FamilyCompletionHomOver.comp
          (canonicalFamilyCompletionMap theta)
          (canonicalFamilyCompletionMap eta) =
        canonicalFamilyCompletionMap
          (FamilySpecMorphism.comp theta eta)

  /-- Every map out of a universal family is the canonical Resolution map
  conjugated by structural equivalences. -/
  familyMapConjugation :
    forall {I : Type v}
      {J : Type w}
      {F : I -> Specification.{u}}
      {G : J -> Specification.{u}}
      (eta : FamilySpecMorphism F G)
      (A : FamilyCompletionObject F)
      (B : FamilyCompletionObject G)
      (hA : IsUniversalFamilyCompletion F A)
      (eF : (i : I) -> Equiv (A.Carrier i) (ResolutionAnswer (F i)))
      (eG : (j : J) -> Equiv (B.Carrier j) (ResolutionAnswer (G j)))
      (heF : IsCanonicalFamilyEquiv F A eF)
      (heG : IsCanonicalFamilyEquiv G B eG)
      (p : FamilyCompletionHomOver eta A B)
      (i : I)
      (x : A.Carrier i),
      p.toFun i x =
        (eG (eta.index i)).symm
          (ResolutionAnswer.map (eta.mapSpec i) (eF i x))

  /-- Structured residual answers are exactly ordinary solutions plus the
  chosen residual vocabulary. -/
  structuredNormalForm :
    forall (E : Type r),
      Nonempty
        (Equiv (ResolutionAnswerWith S E)
          (Sum (Specification.Solution S) E))

  /-- Provenance-aware Strong Totality is simultaneous over arbitrary families
  with a different residual vocabulary in every fiber. -/
  residualFamilyUniversal :
    forall {I : Type v}
      (F : I -> Specification.{u})
      (E : I -> Type r),
      IsUniversalResidualExtensionFamily F E
        (fun i => ResolutionAnswerWith (F i) (E i))
        (fun i => @ResolutionAnswerWith.realize (F i) (E i))
        (fun i q =>
          (ResolutionAnswerWith.residual q :
            ResolutionAnswerWith (F i) (E i)))

  /-- Every universal provenance-aware family is uniquely structurally
  equivalent to the canonical family. -/
  residualFamilyCanonical :
    forall {I : Type v}
      (F : I -> Specification.{u})
      (E : I -> Type r)
      (A : ResidualFamilyCompletionObject F E)
      (hA : IsUniversalResidualFamilyCompletion F E A),
      Exists fun e : (i : I) ->
          Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)) =>
        IsCanonicalResidualFamilyEquiv F E A e ∧
        forall g : (i : I) ->
            Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)),
          IsCanonicalResidualFamilyEquiv F E A g -> g = e

  /-- Universal structured families have the exact fiberwise inhabitation
  criterion: ordinary satisfiability or inhabited residual provenance. -/
  residualFamilyExact :
    forall {I : Type v}
      (F : I -> Specification.{u})
      (E : I -> Type r)
      (A : ResidualFamilyCompletionObject F E)
      (hA : IsUniversalResidualFamilyCompletion F E A)
      (i : I),
      Nonempty (A.Carrier i) ↔
        Specification.Satisfiable (F i) ∨ Nonempty (E i)

  /-- Canonical provenance-aware family transport preserves identities. -/
  residualFamilyFunctorIdentity :
    forall {I : Type v}
      (F : I -> Specification.{u})
      (E : I -> Type r),
      canonicalResidualFamilyCompletionMap
          (FamilySemanticsMorphism.id F E) =
        ResidualFamilyCompletionHomOver.id
          (canonicalResidualFamilyCompletion F E)

  /-- Canonical provenance-aware family transport preserves composition,
  including simultaneous reindexing and residual refinement. -/
  residualFamilyFunctorComposition :
    forall {I : Type v}
      {J : Type w}
      {K : Type z}
      {F : I -> Specification.{u}}
      {E : I -> Type r}
      {G : J -> Specification.{u}}
      {R : J -> Type r}
      {H : K -> Specification.{u}}
      {Q : K -> Type r}
      (eta : FamilySemanticsMorphism F E G R)
      (theta : FamilySemanticsMorphism G R H Q),
      ResidualFamilyCompletionHomOver.comp
          (canonicalResidualFamilyCompletionMap theta)
          (canonicalResidualFamilyCompletionMap eta) =
        canonicalResidualFamilyCompletionMap
          (FamilySemanticsMorphism.comp theta eta)

  /-- Every provenance-aware reindexed family map is the canonical unified
  semantic transport conjugated by structural equivalences. -/
  residualFamilyMapConjugation :
    forall {I : Type v}
      {J : Type w}
      {F : I -> Specification.{u}}
      {E : I -> Type r}
      {G : J -> Specification.{u}}
      {R : J -> Type r}
      (eta : FamilySemanticsMorphism F E G R)
      (A : ResidualFamilyCompletionObject F E)
      (B : ResidualFamilyCompletionObject G R)
      (hA : IsUniversalResidualFamilyCompletion F E A)
      (eF : (i : I) ->
        Equiv (A.Carrier i) (ResolutionAnswerWith (F i) (E i)))
      (eG : (j : J) ->
        Equiv (B.Carrier j) (ResolutionAnswerWith (G j) (R j)))
      (heF : IsCanonicalResidualFamilyEquiv F E A eF)
      (heG : IsCanonicalResidualFamilyEquiv G R B eG)
      (p : ResidualFamilyCompletionHomOver eta A B)
      (i : I)
      (x : A.Carrier i),
      p.toFun i x =
        (eG (eta.index i)).symm
          (FamilySemanticsMorphism.mapAnswer eta i (eF i x))

  /-- Raw syntax lies in the domain of Resolution semantics exactly when it is
  well-formed according to its partial semantic decoder. -/
  wellFormedDomain :
    forall (L : SpecificationLanguage.{u,v}) (c : L.Code),
      Nonempty (L.RawResolution c) ↔ L.WellFormed c

  /-- Requiring every residual to carry a proof of ordinary impossibility has
  exactly the logical strength of propositional excluded middle. -/
  proofCarryingClassicalBoundary :
    (forall Q : Specification.{0},
      Nonempty (ObstructionResolutionAnswer Q)) ↔
    (forall P : Prop, P ∨ Not P)

  /-- Strong Totality cannot be uniformly collapsed back to ordinary
  satisfiability. -/
  noUniformCollapse :
    Not (Nonempty ((Q : Specification.{0}) ->
      ResolutionAnswer Q -> Specification.Solution Q))

  /-- The canonical structured bridge to the existing kernel is lossless. -/
  kernelExact :
    forall {Sigma : Signature.{u}}
      (D : PartialAlg.{u,v} Sigma)
      (e : Expr Sigma D.Carrier),
      decodeKernelExprResolution (kernelExprResolution D e) = Expr.res D e

/-- **Grand Characterization Theorem.**  The canonical Resolution construction
satisfies the complete Strong Totality package: free/minimal completion,
exactness, unique canonicity, functorial and universal naturality, coherent
family extension, structured residual provenance and its full coherence, exact
well-formedness domain, the classical boundary for proof-carrying residuals,
the non-collapse theorem, and exact agreement with the existing kernel
semantics. -/
theorem strongTotality_grandCharacterization
    (S : Specification.{u}) :
    StrongTotalityGrandCharacterization S := by
  refine {
    total := strongTotality S
    freePointed := resolutionAnswer_isUniversalTotalization S
    exact := satisfiable_iff_exists_nonresidual S
    normalForm := ⟨resolutionAnswerEquivSum S⟩
    rigidUniversal := ?_
    uniqueCanonical := ?_
    functorIdentity := ?_
    functorComposition := ?_
    universalNaturality := ?_
    representationInvariant := ?_
    dependentClosure := ?_
    singletonFamily := ?_
    familyUniversal := ?_
    familyClassification := ?_
    familyFunctorIdentity := ?_
    familyFunctorComposition := ?_
    familyMapConjugation := ?_
    structuredNormalForm := ?_
    residualFamilyUniversal := ?_
    residualFamilyCanonical := ?_
    residualFamilyExact := ?_
    residualFamilyFunctorIdentity := ?_
    residualFamilyFunctorComposition := ?_
    residualFamilyMapConjugation := ?_
    wellFormedDomain := fun L c =>
      SpecificationLanguage.rawResolution_nonempty_iff_wellFormed L c
    proofCarryingClassicalBoundary :=
      uniformObstructionResolution_iff_excludedMiddle
    noUniformCollapse := no_uniform_resolutionAnswer_to_solution
    kernelExact := ?_
  }
  · intro X includeSolution residual hX
    exact universalTotalization_rigid
      S X includeSolution residual hX
  · intro X includeSolution residual hX
    exact universalTotalization_unique_structural_equiv
      S X includeSolution residual hX
  · intro a
    exact ResolutionAnswer.map_id S a
  · intro T U g f a
    exact ResolutionAnswer.map_comp g f a
  · intro T f
    exact strongTotality_universalNatural f
  · intro T e
    exact SpecEquiv.strongTotality_representationInvariant e
  · intro T
    exact dependentStrongTotality S T
  · intro X includeSolution residual
    exact isUniversalTotalization_iff_singletonFamily
      S X includeSolution residual
  · intro I F
    exact resolutionAnswerFamily_isUniversalTotalization F
  · intro I F A
    exact universalFamilyCompletion_iff_uniqueCanonicalEquiv F A
  · intro I F
    exact canonicalFamilyCompletionMap_id F
  · intro I J K F G H eta theta
    exact canonicalFamilyCompletionMap_comp eta theta
  · intro I J F G eta A B hA eF eG heF heG p i x
    exact universalFamilyCompletion_map_eq_canonicalConjugate
      eta A B hA eF eG heF heG p i x
  · intro E
    exact ⟨structuredResolutionAnswerEquivSum S E⟩
  · intro I F E
    exact resolutionAnswerWithFamily_isUniversalResidualExtension F E
  · intro I F E A hA
    exact universalResidualFamilyCompletion_uniqueCanonicalEquiv F E A hA
  · intro I F E A hA i
    exact universalResidualExtensionFamily_nonempty_iff
      F E A.Carrier A.includeSolution A.includeResidual hA i
  · intro I F E
    exact canonicalResidualFamilyCompletionMap_id F E
  · intro I J K F E G R H Q eta theta
    exact canonicalResidualFamilyCompletionMap_comp eta theta
  · intro I J F E G R eta A B hA eF eG heF heG p i x
    exact universalResidualFamilyCompletion_map_eq_canonicalConjugate
      eta A B hA eF eG heF heG p i x
  · intro Sigma D e
    exact decode_kernelExprResolution D e

end StrongTotality
end Resolution
