# Resolution Semantics theorem map

The core paper-facing names live in `ResolutionSemantics.lean`; the explicit
one-point facade lives in `ResolutionSemanticsCompletion.lean`; the intrinsic
finite-complement facade lives in `ResolutionIntrinsicFiniteComplementAPI.lean`;
the residual-finiteness and Rees-index comparison lives in
`ResolutionResidualComparisonPublic.lean`;
the finite-base criterion lives in `ResolutionFiniteBasePropernessPublic.lean`;
the arbitrary-base old-fixing-context criterion and its arithmetic instances
live in `ResolutionOldFixingContextPropernessPublic.lean`; their formal
incomparability is recorded in `ResolutionPropernessCriteriaComparison.lean`;
and the original natural-arithmetic facade lives in
`ResolutionArithmeticPropernessPublic.lean`.
Implementation declarations remain available for audit but are not presented
as the main public interface.

## Free compatible completion

- `ResolutionSemantics.freeCompletionUniversal`
- `ResolutionSemantics.expressionKernelQuotientInjective`
- `ResolutionSemantics.expressionKernelQuotientSurjective`

Supporting declarations:

- `Resolution.Free.generatedAns_has_unique_compatibleHom`
- `Resolution.Free.compatibleHom_unique`
- `Resolution.Free.quotientToGenerated_injective`
- `Resolution.Free.quotientToGenerated_surjective`

## Intrinsic finite-complement separation

- `ResolutionSemantics.OutsideOld`
- `ResolutionSemantics.oldOrOutsideEquiv`
- `ResolutionSemantics.outsideEquiv`
- `ResolutionSemantics.intrinsicExtensionHasCanonicalPresentation`
- `ResolutionSemantics.qualitativeFiniteComplementSeparating_theorem`
- `ResolutionSemantics.intrinsicSeparationIffFiniteTag`

Supporting declarations:

- `Resolution.External.OutsideOld`
- `Resolution.External.oldOrOutsideEquiv`
- `Resolution.External.outsideEquiv`
- `Resolution.External.intrinsicExtensionHasCanonicalPresentation`
- `Resolution.External.qualitativeFiniteComplementSeparating_theorem`
- `Resolution.External.intrinsicFiniteComplementSeparatesAt_iff_finiteTagSeparatesAt`

`OutsideOld D T` is the actual complement of the embedded old carrier.  The
primitive budget asks only for an injection of that subtype into `Fin (n+1)`.
`intrinsicExtensionHasCanonicalPresentation` derives a base-fixing injection
into the canonical finite-tag carrier; it does not assert a bijection when the
budget is not tight.  `outsideEquiv` is a genuine bijection only for the
outside part of the canonical finite-tag model.

## Canonical finite-tag consequences

- `ResolutionSemantics.finiteExternalSeparation`
- `ResolutionSemantics.finiteObservationComplete`
- `ResolutionSemantics.finiteSeparationBound`

Supporting declarations:

- `Resolution.External.finiteTagSeparating_theorem`
- `Resolution.External.finiteTag_full_abstraction_verified`
- `Resolution.External.finiteTagSeparatesAt_size_bound`
- `Resolution.External.finiteSeparationRank_le_size`

The paper uses the intrinsic finite-complement theorem as its headline
statement.  Finite external separation and observational completeness are
canonical consequences via the same-budget equivalence.  It does not use
“full abstraction” as a novelty headline.  The constructor-count estimate is a
valid baseline construction bound, not an optimal state-complexity theorem.

## Residual finiteness and the Rees-index distinction

- `ResolutionSemantics.ResidualComparison.finiteBaseCompatibleSeparationBound`
- `ResolutionSemantics.ResidualComparison.finiteBaseGeneratedResiduallyFinite`
- `ResolutionSemantics.ResidualComparison.undefinedApplicationEscapesOldImage`
- `ResolutionSemantics.ResidualComparison.generatedOldClosedIffEvaluatorTotal`

Supporting declarations:

- `Resolution.ResidualComparison.FiniteCompatibleSeparatesAt`
- `Resolution.ResidualComparison.GeneratedResiduallyFinite`
- `Resolution.ResidualComparison.finiteBaseCompatibleSeparationBound`
- `Resolution.ResidualComparison.finiteBaseGeneratedResiduallyFinite`
- `Resolution.ResidualComparison.undefinedApplicationEscapesOldImage`
- `Resolution.ResidualComparison.generatedOldClosed_iff_evaluatorTotal`

If the old carrier injects into `Fin baseSize`, the existing finite-tag
separator becomes a finite compatible target whose whole carrier injects into
`Fin (baseSize + nodeCount x + nodeCount y + 1)`.  Hence the generated Answer
algebra is residually finite for every finitely coded base.  Independently,
the embedded old image is closed under the generated total operations exactly
when the old evaluator is total.  In the genuinely partial case it is therefore
not a total subalgebra, so the finite-complement inclusion is not literally an
ordinary finite-Rees-index inclusion.

## Completion, properness, and equations

- `ResolutionSemantics.completedAlgebra`
- `ResolutionSemantics.completionComplete`
- `ResolutionSemantics.equationConservative`
- `ResolutionSemantics.OnePointCompletion.embeddingNotSurjective`
- `ResolutionSemantics.OnePointCompletion.addsPoint`
- `ResolutionSemantics.FiniteBaseCompletion.completeIffTotal`
- `ResolutionSemantics.FiniteBaseCompletion.embeddingSurjectiveIffTotal`
- `ResolutionSemantics.FiniteBaseCompletion.embeddingNotSurjectiveIffExistsUndefined`
- `ResolutionSemantics.OldFixingContextCompletion.factorialSequenceCauchy`
- `ResolutionSemantics.OldFixingContextCompletion.factorialSequenceNoLimit`
- `ResolutionSemantics.OldFixingContextCompletion.everyFiniteStageNotEquality`
- `ResolutionSemantics.OldFixingContextCompletion.separationRankGreaterThanBudget`
- `ResolutionSemantics.OldFixingContextCompletion.notComplete`
- `ResolutionSemantics.OldFixingContextCompletion.embeddingNotSurjective`
- `ResolutionSemantics.OldFixingContextCompletion.addsPoint`
- `ResolutionSemantics.PropernessCriteria.onePointProperWithoutOldFixing`
- `ResolutionSemantics.PropernessCriteria.natProperWithoutFiniteCoding`
- `ResolutionSemantics.NatDivision.stageZeroNotSeparating`
- `ResolutionSemantics.NatDivision.everyFiniteStageNotEquality`
- `ResolutionSemantics.NatDivision.factorialAddZeroCauchy`
- `ResolutionSemantics.NatDivision.factorialAddZeroNoLimit`
- `ResolutionSemantics.NatDivision.notComplete`
- `ResolutionSemantics.NatDivision.completionEmbeddingNotSurjective`
- `ResolutionSemantics.NatDivision.completionAddsPoint`
- `ResolutionSemantics.NatDivision.oldFixingCriterion`
- `ResolutionSemantics.NatDivision.separationRanksUnbounded`
- `ResolutionSemantics.IntDivision.everyFiniteStageNotEquality`
- `ResolutionSemantics.IntDivision.factorialOldFixingCauchy`
- `ResolutionSemantics.IntDivision.factorialOldFixingNoLimit`
- `ResolutionSemantics.IntDivision.notComplete`
- `ResolutionSemantics.IntDivision.completionEmbeddingNotSurjective`
- `ResolutionSemantics.IntDivision.completionAddsPoint`
- `ResolutionSemantics.IntDivision.separationRanksUnbounded`

Supporting declarations:

- `Resolution.External.completedResolutionTotalAlg`
- `Resolution.External.completedResolutionFilteredTotalAlg_complete`
- `Resolution.External.FilteredTotalAlg.completedResolutionFilteredAlgebra_initial`
- `Resolution.External.completionConstantEquation_iff_generatedConstantEquation`
- `Resolution.OnePoint.factorialCombs_cauchy`
- `Resolution.OnePoint.noLimit`
- `Resolution.OnePoint.not_complete`
- `Resolution.OnePoint.completionWitness_ne_embed`
- `Resolution.OnePoint.completionEmbedding_not_surjective`
- `Resolution.OnePoint.completion_adds_point`
- `Resolution.FiniteBaseProperness.factorialCombs_cauchy`
- `Resolution.FiniteBaseProperness.factorialCombs_noLimit`
- `Resolution.FiniteBaseProperness.not_complete_of_coded_of_undefined`
- `Resolution.FiniteBaseProperness.complete_iff_total`
- `Resolution.FiniteBaseProperness.completionEmbedding_not_surjective_iff_exists_undefined`
- `Resolution.OldFixingContextProperness.factorialIterates_cauchy`
- `Resolution.OldFixingContextProperness.factorialIterates_noLimit`
- `Resolution.OldFixingContextProperness.every_stage_not_equality`
- `Resolution.OldFixingContextProperness.factorialPair_separationRank_gt`
- `Resolution.OldFixingContextProperness.not_complete`
- `Resolution.OldFixingContextProperness.completionWitness_ne_embed`
- `Resolution.OldFixingContextProperness.completionEmbedding_not_surjective`
- `Resolution.OldFixingContextProperness.completion_adds_point`
- `Resolution.ArithmeticProperness.stageZero_not_separating`
- `Resolution.ArithmeticProperness.every_stage_not_equality`
- `Resolution.ArithmeticProperness.factorialAddZeros_cauchy`
- `Resolution.ArithmeticProperness.factorialAddZeros_noLimit`
- `Resolution.ArithmeticProperness.not_complete`
- `Resolution.ArithmeticProperness.completionWitness_ne_embed`
- `Resolution.ArithmeticProperness.completionEmbedding_not_surjective`
- `Resolution.ArithmeticProperness.completion_adds_point`

For a finitely coded old carrier, the completion is proper exactly when at
least one old application is undefined.  The one-point result is the smallest
explicit corollary.  For an arbitrary old carrier, an undefined old seed plus
a context `x ↦ u(x,e)` fixing every old element is sufficient for properness.
Its factorial orbit is Cauchy with no generated limit, every finite stage is
strictly coarser than equality, and explicit stage-`m` pairs have separation
rank greater than `m`.  Natural and integer arithmetic both instantiate this
criterion with `0 / 0` and `x ↦ x + 0`.

The two properness hypotheses are incomparable.  The one-point
always-undefined algebra has a one-state code and a proper completion but no
old-fixing-context witness.  Natural arithmetic has the old-fixing witness
`x ↦ x + 0` and a proper completion, but `Nat` admits no injection into any
finite code bound.  The latter fact is proved from the repository's explicit
pigeonhole theorem.

## Distinction from prefix-depth completion

- `Resolution.Probe.observational_strictly_finer_than_depth`
- `Resolution.Probe.comb_separatesAt_one`
- `Resolution.Probe.NatProbe.natComb_pairwise_separated_at_zero`

These theorems show that fixed finite observational budgets can detect arbitrarily deep comb differences. They also show that the general linear tag bound is far from tight on this family.

## Arithmetic examples

Natural numbers:

- `ResolutionSemantics.NatDivision.singularFamilyInjective`
- `ResolutionSemantics.NatDivision.singularFamilyDisjoint`
- `ResolutionSemantics.NatDivision.stageZeroNotSeparating`
- `ResolutionSemantics.NatDivision.everyFiniteStageNotEquality`
- `ResolutionSemantics.NatDivision.factorialAddZeroCauchy`
- `ResolutionSemantics.NatDivision.factorialAddZeroNoLimit`
- `ResolutionSemantics.NatDivision.notComplete`
- `ResolutionSemantics.NatDivision.completionEmbeddingNotSurjective`
- `ResolutionSemantics.NatDivision.completionAddsPoint`
- `ResolutionSemantics.NatDivision.oldFixingCriterion`
- `ResolutionSemantics.NatDivision.separationRanksUnbounded`

Integers:

- `ResolutionSemantics.IntDivision.singularFamilyInjective`
- `ResolutionSemantics.IntDivision.zeroDivZeroNotOld`
- `ResolutionSemantics.IntDivision.everyFiniteStageNotEquality`
- `ResolutionSemantics.IntDivision.factorialOldFixingCauchy`
- `ResolutionSemantics.IntDivision.factorialOldFixingNoLimit`
- `ResolutionSemantics.IntDivision.notComplete`
- `ResolutionSemantics.IntDivision.completionEmbeddingNotSurjective`
- `ResolutionSemantics.IntDivision.completionAddsPoint`
- `ResolutionSemantics.IntDivision.separationRanksUnbounded`

The manuscript does not state that `0 / 0` is an ordinary number. It states that it is a structured completed Answer outside the old numerical image.
