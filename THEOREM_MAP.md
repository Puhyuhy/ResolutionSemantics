# Resolution Semantics theorem map

The publication-facing structural facade is
`lean/ResolutionMasterTheorems.lean`. The manuscript is organized around the
following dependency chain rather than around the historical order in which the
individual properness lemmas were developed.

## 1. Free compatible completion substrate

Headline declarations:

- `ResolutionSemantics.freeCompletionUniversal`
- `ResolutionSemantics.expressionKernelQuotientInjective`
- `ResolutionSemantics.expressionKernelQuotientSurjective`

This is the normalized free-compatible-completion substrate. It is established
partial-algebra infrastructure and is not the paper's novelty headline.

## 2. Master I — relative finite-pattern realization

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
pointwise. Pairwise finite-tag separation is the two-point consequence. The
older pair-specific implementation retains the explicit constructor-size bound.

The intrinsic observer budget counts only genuinely outside states. The base may
therefore be infinite. Canonical finite-tag carriers have the form
`D.Carrier ⊔ Fin(n) ⊔ {overflow}`. The intrinsic/canonical correspondence is
recorded by:

- `ResolutionSemantics.OutsideOld`
- `ResolutionSemantics.oldOrOutsideEquiv`
- `ResolutionSemantics.outsideEquiv`
- `ResolutionSemantics.intrinsicExtensionHasCanonicalPresentation`
- `ResolutionSemantics.intrinsicSeparationIffFiniteTag`

A supporting obstruction explains why finite-family realization over an
infinite fixed base is not obtained by the standard residual-finiteness product
trick. `ResolutionRelativeProductObstruction.lean` proves at carrier level that
both embeddings `Nat -> Nat ⊕ Unit` have finite relative complement, while the
diagonal embedding into their Cartesian product does not. The product contains
infinitely many mixed outside points `(a, star)`. The headline declaration is:

- `ResolutionSemantics.RelativeObservers.finiteRelativeComplement_not_closed_under_binary_products`

Thus the restricted observer class is not binary-product closed over an
infinite base, so the direct finite-pattern construction in Master I performs
work that cannot be replaced by simply multiplying pairwise separators inside
the same class.

## 3. Observational filtration and completed algebra

Headline declarations:

- `ResolutionSemantics.completedAlgebra`
- `ResolutionSemantics.completionComplete`
- `Resolution.External.FilteredTotalAlg.completedResolutionFilteredAlgebra_initial`
- `ResolutionSemantics.equationConservative`

The finite-tag stages induce a separated filtration. Cauchy sequences modulo
stagewise eventual agreement form the observational completion. Primitive
operations extend continuously, and the completed algebra preserves and
reflects exactly the constant-bearing universal equations of the generated
Answer algebra.

The prefix-depth comparison is formally witnessed by
`Resolution.Probe.depthCauchy_not_observationalCauchy`, so this is not simply
the classical tree-prefix completion under different notation.

## 4. Master II — relative trajectory compression

Headline declaration:

- `ResolutionSemantics.MasterTheorems.orbitCompressionCauchy`

Core module: `ResolutionOrbitCompressionMaster.lean`.

At every stage only the deterministic observer trajectory relevant to the
chosen generated unary family needs a finite code. The whole observer carrier
may remain infinite. Standard pigeonhole periodicity plus factorial divisibility
gives the Cauchy half; this finite-dynamics argument is explicitly background
machinery rather than a novelty claim.

## 5. Finite-pattern escape — the anti-limit mechanism

Headline declaration:

- `ResolutionSemantics.MasterTheorems.finitePatternEscapeNoGeneratedLimit`

Core module: `ResolutionFinitePatternAntiLimit.lean`.

For growing unary syntax
`t_(k+1) = susp(u, t_k, old(e))`, a candidate-tailored finite-pattern observer
realizes a generated candidate and a sufficiently long orbit prefix exactly.
The next unseen iterate falls outside the selected finite subterm pattern and is
sent to overflow; overflow is absorbing along the continuation. Hence no
generated Answer can be the limit of the factorial sample.

This theorem is independent of finite-state periodicity. It is the
Resolution-specific no-limit half of the properness argument.

## 6. Combined compression–escape properness theorem

Headline declarations:

- `ResolutionSemantics.MasterTheorems.compressedEscapingOrbitNotComplete`
- `ResolutionSemantics.MasterTheorems.compressedEscapingOrbitEmbeddingNotSurjective`

Logical form:

`finite trajectory compression + finite-pattern escape`

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

When the old carrier injects into `Fin(baseSize)`, the whole stage observer is
finite, so trajectory compression is automatic. The exact criterion is:
`completion proper <=> some base application undefined`.

Finite-base residual-finiteness consequences remain available through:

- `ResolutionSemantics.ResidualComparison.finiteBaseCompatibleSeparationBound`
- `ResolutionSemantics.ResidualComparison.finiteBaseGeneratedResiduallyFinite`
- `ResolutionSemantics.ResidualComparison.generatedOldClosedIffEvaluatorTotal`

The qualitative finite-signature ground-term residual-finiteness subcase is
positioned as classical recognizability, not new mathematics.

## 8. Infinite-base old-fixing instance

Headline declarations:

- `ResolutionSemantics.MasterTheorems.oldFixingPropernessViaCombinedMaster`
- `ResolutionSemantics.MasterTheorems.oldFixingRanksUnbounded`

Related public declarations:

- `ResolutionSemantics.OldFixingContextCompletion.factorialSequenceCauchy`
- `ResolutionSemantics.OldFixingContextCompletion.factorialSequenceNoLimit`
- `ResolutionSemantics.OldFixingContextCompletion.embeddingNotSurjective`

If an undefined seed exists and a unary context fixes every old element
pointwise, the relevant observer trajectory has finite external complexity even
when the old carrier itself is infinite. The sharp checked stage witness is
`c_(n+1)! ~_n c_(n+2)!`, and therefore the least finite separation rank is
strictly greater than `n`.

The finite-base and old-fixing hypotheses are incomparable; the supporting
comparison lives in `ResolutionPropernessCriteriaComparison.lean`.

## 9. Arithmetic instances

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

The undefined seed is `0/0`; the old-fixing context is `x ↦ x + 0`. Division by
zero remains a structured unresolved Answer rather than an ordinary number.

## 10. Many-sorted Diaconescu provenance bridge

The bridge is supporting formalization of established partial-to-total
infrastructure, not a third novelty axis.

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

Relevant modules:

- `ResolutionDiaconescuEncoding.lean`
- `ResolutionDiaconescuManySorted.lean`
- `ResolutionDiaconescuContinuation.lean`
- `ResolutionDiaconescuAdjunction.lean`
- `ResolutionDiaconescuBinarySpecialization.lean`
- `ResolutionConditionalInitial.lean`
- `ResolutionDiaconescuInitialExistence.lean`

The formalization covers the fixed-signature operations-only fragment used by
the paper: arbitrary finite arities, separate total/partial operation families,
the satisfaction condition, recovery, persistent liberality, hom-set
adjunction laws, semantic consequence, initiality transfers, and the
singleton-sort binary specialization. Arbitrary signature morphisms and the
full institution/comorphism layer remain outside scope.

## 11. Formal audit

`lean/AxiomAudit.lean` checks every manuscript-linked declaration and prints
axiom dependencies for the principal theorems. `scripts/verify.sh` accepts only
Lean's standard:

- `propext`
- `Classical.choice`
- `Quot.sound`

The promoted manuscript/API checker additionally requires the master-theorem
headlines above and rejects superseded old-fixing indexing.
