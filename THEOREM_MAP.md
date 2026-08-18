# Resolution Semantics theorem map

The publication-facing structural facade is implemented in
`lean/ResolutionMasterTheorems.lean`.  The namespace/file name is retained as a
stable Lean API identifier; the mathematical exposition uses descriptive names
for the results.

## 1. Free compatible completion substrate

Headline declarations:

- `ResolutionSemantics.freeCompletionUniversal`
- `ResolutionSemantics.expressionKernelQuotientInjective`
- `ResolutionSemantics.expressionKernelQuotientSurjective`

This is established partial-algebra infrastructure and is not a novelty
headline.

## 2. Relative finite-pattern realization

Headline declarations:

- `ResolutionSemantics.MasterTheorems.relativeFinitePatternRealization`
- `ResolutionSemantics.MasterTheorems.relativeFiniteComplementSeparation`
- `ResolutionSemantics.finiteSeparationBound`
- `ResolutionSemantics.finiteObservationComplete`

Core modules:

- `ResolutionFinitePatternRealization.lean`
- `ResolutionFinitePatternRealizationPublic.lean`
- `ResolutionIntrinsicFiniteComplement.lean`
- `ResolutionIntrinsicFiniteComplementAPI.lean`
- `ResolutionFiniteTagProof.lean`

One compatible finite-complement observer is simultaneously injective on any
chosen finite family of generated Answers while fixing the entire partial base
pointwise.  Pairwise separation is the two-point consequence.  The older
pair-specific implementation retains the explicit constructor-size bound.

The observer budget counts only genuinely outside states, so the base may be
infinite.  The intrinsic/canonical correspondence is recorded by:

- `ResolutionSemantics.OutsideOld`
- `ResolutionSemantics.oldOrOutsideEquiv`
- `ResolutionSemantics.outsideEquiv`
- `ResolutionSemantics.intrinsicExtensionHasCanonicalPresentation`
- `ResolutionSemantics.intrinsicSeparationIffFiniteTag`

The supporting product obstruction is:

- `ResolutionSemantics.RelativeObservers.finiteRelativeComplement_not_closed_under_binary_products`

It proves that the restricted observer class is not binary-product closed over
an infinite base, so the finite-family theorem is not recovered inside the
same class by multiplying pairwise separators.

## 3. Observational filtration and completed algebra

Headline declarations:

- `ResolutionSemantics.completedAlgebra`
- `ResolutionSemantics.completionComplete`
- `Resolution.External.FilteredTotalAlg.completedResolutionFilteredAlgebra_initial`
- `ResolutionSemantics.equationConservative`

Finite-tag stages induce a separated filtration.  Cauchy sequences modulo
stagewise eventual agreement form the observational completion.  Primitive
operations extend continuously, and the completed algebra preserves and
reflects exactly the constant-bearing universal equations of the generated
Answer algebra.

## 4. Trajectory compression

Headline declaration:

- `ResolutionSemantics.MasterTheorems.orbitCompressionCauchy`

Core module: `ResolutionOrbitCompressionMaster.lean`.

Only the deterministic observer trajectory relevant to the chosen generated
unary family needs a finite code.  The full observer carrier may remain
infinite.  Pigeonhole periodicity plus factorial divisibility gives the Cauchy
half; this finite-dynamics argument is background machinery.

## 5. Relative finite-pattern escape

Headline declaration:

- `ResolutionSemantics.MasterTheorems.finitePatternEscapeNoGeneratedLimit`

Core modules:

- `ResolutionFinitePatternAntiLimit.lean`
- `ResolutionRelativeEscapeComparison.lean`

For growing unary syntax, a candidate-tailored finite-pattern observer realizes
the candidate and a sufficiently long orbit prefix exactly, sends the first
unseen continuation to overflow, and keeps the later tail there.  Thus no
generated Answer is the limit of the factorial sample.

The structural comparison with ordinary finite-target recognition is exposed by:

- `Resolution.RelativeEscapeComparison.no_finitely_coded_target_with_injective_base`
- `Resolution.RelativeEscapeComparison.relativeEscapeBeyondOrdinaryFiniteTargets`
- `Resolution.RelativeEscapeComparison.natRelativeEscapeBeyondOrdinaryFiniteTargets`

When the pointwise-preserved base is not finitely codable, the actual escape
observer is globally non-finite while retaining only finite external
complexity.  The abstract anti-limit pattern itself is not claimed as new.

## 6. Compression--escape properness

Headline declarations:

- `ResolutionSemantics.MasterTheorems.compressedEscapingOrbitNotComplete`
- `ResolutionSemantics.MasterTheorems.compressedEscapingOrbitEmbeddingNotSurjective`

Logical form:

`finite trajectory compression + relative finite-pattern escape`

`=> factorial Cauchy + no generated limit`

`=> incomplete generated filtered space`

`=> proper observational completion`.

This is the structural center of the promoted manuscript.

## 7. Finite-base instance

Headline declaration:

- `ResolutionSemantics.MasterTheorems.finiteBasePropernessCriterion`

Equivalent public results include:

- `ResolutionSemantics.FiniteBaseCompletion.completeIffTotal`
- `ResolutionSemantics.FiniteBaseCompletion.embeddingNotSurjectiveIffExistsUndefined`

For a finitely coded base, the completion is proper exactly when some base
application is undefined.

Finite-base residual-finiteness consequences remain available through:

- `ResolutionSemantics.ResidualComparison.finiteBaseCompatibleSeparationBound`
- `ResolutionSemantics.ResidualComparison.finiteBaseGeneratedResiduallyFinite`
- `ResolutionSemantics.ResidualComparison.generatedOldClosedIffEvaluatorTotal`

The qualitative finite-signature ground-term residual-finiteness subcase is
positioned as classical recognizability.

## 8. Infinite-base old-fixing instance

Headline declarations:

- `ResolutionSemantics.MasterTheorems.oldFixingPropernessViaCombinedMaster`
- `ResolutionSemantics.MasterTheorems.oldFixingRanksUnbounded`

Related public declarations:

- `ResolutionSemantics.OldFixingContextCompletion.factorialSequenceCauchy`
- `ResolutionSemantics.OldFixingContextCompletion.factorialSequenceNoLimit`
- `ResolutionSemantics.OldFixingContextCompletion.embeddingNotSurjective`

An undefined seed plus a unary context fixing every base element pointwise
provides trajectory compression even over an infinite base.  The sharp checked
stage witness is `c_(n+1)! ~_n c_(n+2)!`, giving unbounded least finite-tag
separation ranks.

## 9. Prefix-depth contrast

Headline declarations:

- `Resolution.Probe.depthCauchy_not_observationalCauchy`
- `Resolution.Probe.comb_separatesAt_one`
- `Resolution.Probe.NatProbe.natComb_pairwise_separated_at_zero`

The same unresolved comb sequence is Cauchy for prefix-depth agreement but not
for Resolution observation.  One fixed one-tag observer separates adjacent
combs at arbitrary depth; in Nat, a zero-tag observer separates all distinct
combs.  Therefore the two uniformities are genuinely different.

## 10. Arithmetic instances

Natural arithmetic:

- `ResolutionSemantics.NatDivision.singularFamilyInjective`
- `ResolutionSemantics.NatDivision.singularFamilyDisjoint`
- `ResolutionSemantics.NatDivision.oldFixingCriterion`
- `ResolutionSemantics.NatDivision.separationRanksUnbounded`

Integer arithmetic:

- `ResolutionSemantics.IntDivision.singularFamilyInjective`
- `ResolutionSemantics.IntDivision.zeroDivZeroNotOld`
- `ResolutionSemantics.IntDivision.completionEmbeddingNotSurjective`
- `ResolutionSemantics.IntDivision.separationRanksUnbounded`

The undefined seed is `0/0`; the base-fixing context is `x ↦ x + 0`.  Division
by zero remains a structured unresolved Answer rather than an ordinary number.

## 11. Many-sorted Diaconescu provenance bridge

The bridge is supporting formalization of established partial-to-total
infrastructure, not a separate novelty axis.

Core declarations include:

- `Resolution.Diaconescu.ManySorted.term_evalPartial_sound`
- `Resolution.Diaconescu.ManySorted.term_evalPartial_complete`
- `Resolution.Diaconescu.ManySorted.alpha_satisfaction_condition`
- `Resolution.Diaconescu.ManySorted.gamma_satisfiesGamma`
- `Resolution.Diaconescu.ManySorted.betaGammaPartialAlgEquiv`
- `Resolution.Diaconescu.ManySorted.gamma_persistent_liberality`
- `Resolution.Diaconescu.ManySorted.gammaBetaHomEquiv`
- `Resolution.Diaconescu.ManySorted.semantic_consequence_equivalence`
- `Resolution.Diaconescu.ManySorted.gamma_preserves_initiality`
- `Resolution.Diaconescu.ManySorted.beta_of_initial_encoded_is_initial`
- `Resolution.Diaconescu.InitialExistence.quasiTheory_has_initial_partial_model`
- `Resolution.Diaconescu.BinarySpecialization.generatedEquiv`
- `Resolution.Diaconescu.BinarySpecialization.gammaEquiv`

The formalization covers the fixed-signature operations-only fragment used by
the paper: arbitrary finite arities, separate total/partial operation families,
the satisfaction condition, recovery, persistent liberality, hom-set
adjunction laws, semantic consequence, initiality transfers, and the
singleton-sort binary specialization.

## 12. Formal audit

`lean/AxiomAudit.lean` checks every manuscript-linked declaration and prints
axiom dependencies for the principal results. `scripts/verify.sh` accepts only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.
The promoted manuscript/API checker rejects stale theorem indexing and missing
paper-facing declarations.
