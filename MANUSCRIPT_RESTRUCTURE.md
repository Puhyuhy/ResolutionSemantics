# Manuscript restructure map

This file records the branch-only editorial reconstruction of the paper around
the checked master-theorem architecture. The reconstruction has passed its
promotion gate and is now the official manuscript source on the working branch.

## Safety rule and current state

- Working branch: `agent/relative-pattern-orbit-compression`.
- PR #6 remains draft and must not be merged during the restructuring audit.
- `paper/latex/revised.tex` now uses the promoted master-theorem structure.
- `paper/Resolution_Semantics_Adrian_Puha.pdf` was rebuilt deterministically
  from the promoted source and committed by branch CI.
- The strict `build-paper.sh --check-committed` guardrail has been restored.
- `paper/latex/restructured.tex` and the `restructured-*.tex` files remain as
  the audited section source/preview path during branch review.

## Old presentation -> promoted role

| Existing result / section | Promoted role |
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
| Earlier old-fixing factorial indexing | Superseded by the sharp `(m+1)!/(m+2)!` witness |
| Exact equation preservation | Independent major consequence of the completed filtered algebra |
| Natural/integer arithmetic | Concrete infinite-base instances of combined mechanism |
| Diaconescu many-sorted formalization | Provenance/compatibility layer, not a third novelty axis |

## Promoted logical spine

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

These declarations are included in `lean/AxiomAudit.lean` and in the official
manuscript/API checker.

## Novelty discipline

Do not claim novelty for:

- free compatible completion itself;
- finite selected-subterm/sink constructions in isolation;
- finite-state eventual periodicity;
- factorial synchronization;
- the generic implication from a nonconvergent Cauchy sequence to
  incompleteness;
- Diaconescu's encoding or its established adjunction theory.

The strongest defensible novelty target is the interaction of:

- a pointwise-preserved possibly infinite partial base;
- finite complexity only outside that base;
- simultaneous finite-pattern realization;
- trajectory-level rather than carrier-level compression;
- finite-pattern escape witnesses that exclude every finite generated candidate;
- resulting proper observational completions and their finite/infinite-base instances.

## Promotion gate — passed

The branch promotion was accepted only after all of the following succeeded:

1. `bash scripts/verify.sh` with the expanded master-theorem axiom audit.
2. Independent build of the restructured preview with no unresolved
   citations/references.
3. Visual inspection of the preview, including the abstract and the central
   compression/escape theorem pages.
4. Official manuscript/API checking against every cited `\leanname{...}`.
5. Deterministic rebuild of the promoted official PDF.
6. Visual inspection of the official 18-page PDF and its metadata.
7. CI commit of that exact PDF on the working branch.
8. Restoration and successful execution of
   `bash scripts/build-paper.sh --check-committed`, confirming byte-for-byte
   agreement between promoted source and committed PDF.
9. Explicit scope language separating standard machinery from
   Resolution-specific claims.
10. Use of the sharp old-fixing `(n+1)!/(n+2)!` stage witness.

The branch remains a review branch; passing this gate is not a recommendation
to merge PR #6.
