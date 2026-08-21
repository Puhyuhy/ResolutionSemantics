# Paper I — Academic Rebuild Plan

Status: **rewrite branch only**

This branch rebuilds the manuscript as a conventional mathematics paper. The existing manuscript on `main` remains preserved as the historical version reviewed externally.

## Editorial premise

The paper must stand on its own for a mathematician who never opens GitHub and never reads Lean source.

Lean is verification support, not the narrative spine.

## Gate before prose

Before drafting a new introduction, the project must be able to complete the sentence:

> **The genuinely new mathematical statement of this paper is:** …

The answer must use standard mathematical language rather than internal Lean identifiers or project slogans.

## Candidate theorem spine to audit first

The rewrite should be built backward from at most 3–5 mathematically central results. Current candidates are:

1. **Relative finite-pattern realization.** For any finite family of generated elements, construct one compatible total extension that fixes the entire partial base pointwise, has finite complement outside the base, and is injective on the chosen family.
2. **Product obstruction.** Over an infinite fixed base, the class of pointwise-base-fixing finite-complement observers is not in general closed under binary products; therefore finite-family realization is not obtained formally by multiplying pairwise separators.
3. **Compression–escape properness.** Combine finite trajectory compression with relative finite-pattern escape to produce a Cauchy trajectory with no generated limit, hence a proper observational completion.
4. **Finite-base classification.** In the finite-base case, characterize when the observational completion is proper in terms of totality/undefined operations.
5. **Infinite-base base-fixing consequences.** Under a base-fixing context hypothesis, obtain incompleteness/properness and unbounded separation ranks.

These are candidates, not publication claims. Each requires theorem-level novelty comparison before manuscript promotion.

## What is background, not a headline contribution

The rewrite must visibly treat the following as established machinery unless a stronger precise theorem is independently justified:

- free completion of partial algebras;
- term-algebra / quotient / kernel presentations;
- generic residual/discrimination terminology;
- generic Cauchy/profinite-style completion machinery;
- finite-orbit periodicity/compression by itself;
- tree metrics and ordinary infinite-tree completion;
- the many-sorted Diaconescu encoding bridge;
- standard universal-algebra and category-theoretic uniqueness arguments.

## Required writing order

1. theorem-level novelty audit;
2. standard notation and terminology map;
3. mathematical architecture and dependency graph;
4. full human-readable definitions and proofs;
5. examples;
6. related work and limitations;
7. introduction;
8. abstract and conclusion;
9. Lean theorem ↔ manuscript theorem appendix;
10. hostile referee pass and skim test;
11. build/release decision.

## Human-proof requirement

Every central theorem must have a proof in the manuscript that is mathematically checkable without Lean. The formalization may certify the proof but may not substitute for it.

Routine lemmas may be summarized, but no essential logical step may be hidden behind a theorem name.

## Vocabulary policy

- Prefer standard partial-algebra and universal-algebra terminology whenever available.
- Internal Lean identifiers such as `GeneratedAns`, `MasterTheorems`, or historical `old*` names should not control exposition.
- Use `base` rather than `old` in prose unless quoting source identifiers.
- Do not use `profinite` unless an actual inverse-limit theorem in the appropriate relative category has been established.
- Do not use `full abstraction` as a novelty label.

## Novelty wording policy

Allowed before external confirmation:

- “we prove …”
- “our construction has the following property …”
- “we did not locate an exact precedent in the sources audited …”
- “candidate contribution …”

Not allowed without stronger evidence:

- “first”
- “novel”
- “new theory”
- “previously unknown”
- “breakthrough”

## Lean role

The formalization should eventually provide:

- exact declaration names for central statements;
- a small paper-facing API;
- axiom audit;
- reproducible compilation;
- theorem-to-prose alignment checks.

The manuscript should not read like an API reference.

## Rewrite policy

Do **not** line-edit the historical manuscript into compliance. Reconstruct the paper from the theorem spine and standard literature outward. Reuse correct mathematical content, references, examples, and proofs only after re-expressing them in normal mathematical form.

No changes from this branch should be merged into `main` until the rewritten manuscript passes both the novelty gate and the academic-writing gate.
