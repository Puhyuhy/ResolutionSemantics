# Manuscript restructure map

This file records the branch-only editorial reconstruction of the paper around the checked master-theorem architecture. It is not part of the mathematical API and does not replace the stable manuscript until the preview has passed CI and review.

## Safety rule

- Working branch: `agent/relative-pattern-orbit-compression`.
- PR #6 remains draft and must not be merged during the restructuring audit.
- `paper/latex/revised.tex` and the committed review PDF remain the stable fallback until explicit promotion on this branch.
- The experimental manuscript is `paper/latex/restructured.tex` plus `restructured-*.tex` section files.

## Old presentation -> new role

| Existing result / section | New role |
|---|---|
| Normalized generated Answer algebra | Established free-compatible-completion substrate |
| Free compatible completion | Background/foundation, retained but not novelty headline |
| Pairwise finite-tag separator | Two-point corollary of Master I; quantitative size bound retained |
| Intrinsic finite-complement observer class | Core Resolution-specific observer framework |
| Finite-pattern realization | **Master I** |
| Stage filtration and Cauchy quotient | Standard filtered-completion machinery induced by Master I |
| Finite-base factorial comb argument | Instance of trajectory compression + finite-pattern escape |
| Old-fixing factorial orbit | Infinite-base instance of the same combined mechanism |
| Finite-state/factorial periodicity | Standard dynamics; explicitly not a novelty claim |
| Candidate/prefix + overflow no-limit proof | Generalized to **finite-pattern escape** |
| Abstract orbit coding | **Master II: trajectory compression** |
| Compression + escape | **Combined properness theorem / structural center** |
| Finite-base properness iff evaluator partial | Exact finite-base instance/corollary |
| Old-fixing properness | Arbitrary-base sufficient instance/corollary |
| `(m+2)!/(m+3)!` old-fixing witness | Superseded by sharper `(m+1)!/(m+2)!` witness |
| Exact equation preservation | Independent major consequence of the completed filtered algebra |
| Natural/integer arithmetic | Concrete infinite-base instances of combined mechanism |
| Diaconescu many-sorted formalization | Provenance/compatibility layer, not a third novelty axis |

## New logical spine

1. **Free compatible completion substrate.**
2. **Master I — relative finite-pattern realization.**
3. Finite-tag filtration and observational completion.
4. **Master II — finite trajectory compression**, yielding factorial Cauchy behavior.
5. **Finite-pattern escape**, yielding no generated limit for growing unary syntax.
6. **Combined compression–escape properness theorem.**
7. Finite-base and old-fixing theorems as formally checked instances.
8. Exact equational conservativity and arithmetic examples.
9. Diaconescu bridge and prior-work positioning.

## Publication-facing Lean declarations

- `ResolutionSemantics.MasterTheorems.relativeFinitePatternRealization`
- `ResolutionSemantics.MasterTheorems.relativeFiniteComplementSeparation`
- `ResolutionSemantics.MasterTheorems.orbitCompressionCauchy`
- `ResolutionSemantics.MasterTheorems.finitePatternEscapeNoGeneratedLimit`
- `ResolutionSemantics.MasterTheorems.compressedEscapingOrbitNotComplete`
- `ResolutionSemantics.MasterTheorems.compressedEscapingOrbitEmbeddingNotSurjective`
- `ResolutionSemantics.MasterTheorems.finiteBasePropernessCriterion`
- `ResolutionSemantics.MasterTheorems.oldFixingPropernessViaCombinedMaster`
- `ResolutionSemantics.MasterTheorems.oldFixingRanksUnbounded`

These declarations are now included in `lean/AxiomAudit.lean`.

## Novelty discipline

Do not claim novelty for:

- free compatible completion itself;
- finite selected-subterm/sink constructions in isolation;
- finite-state eventual periodicity;
- factorial synchronization;
- the tautology that a Cauchy sequence with no limit witnesses incompleteness;
- Diaconescu's encoding or its established adjunction theory.

The strongest defensible novelty target is the interaction of:

- a pointwise-preserved possibly infinite partial base;
- finite complexity only outside that base;
- simultaneous finite-pattern realization;
- trajectory-level rather than carrier-level compression;
- finite-pattern escape witnesses that exclude every finite generated candidate;
- resulting proper observational completions and their finite/infinite-base instances.

## Promotion gate

Do not replace `revised.tex` with the restructured manuscript until all of the following hold:

1. `bash scripts/verify.sh` passes with the expanded master-theorem axiom audit.
2. `bash scripts/build-paper.sh --check-committed` still passes for the stable manuscript.
3. `bash scripts/build-restructured-paper.sh` passes with no unresolved citations/references.
4. The restructured PDF is visually inspected for theorem flow, layout, and obvious prose regressions.
5. Every new `\leanname{...}` in the promoted manuscript is present in `AxiomAudit.lean`.
6. The contribution/scope section distinguishes standard machinery from Resolution-specific claims.
7. The old-fixing statement uses the sharpened `(n+1)!/(n+2)!` bound.
