# A Finite-Complement Congruence Topology for Partial Algebras

Author: **Adrian Puha**

This branch contains a shortened manuscript about a congruence topology induced
by compatible total extensions of a partial algebra that retain the original
carrier pointwise and add only finitely many elements outside it.

The mathematical paper is under `paper/latex/`, with `paper.tex` as the root.
The accompanying Lean development is supplementary verification and is not
needed to read or check the proofs in the manuscript.

## Mathematical content

Let `D` be a partial algebra with carrier `A`, and let `F(D)` denote its free
compatible total extension.

A **finite-complement compatible extension** is a compatible total algebra `T`
that contains `A` pointwise and satisfies `|T \ A| < infinity`.

The manuscript uses these extensions in three steps:

1. **Finite separation.** A finite subterm closure is retained and its
   complement is collapsed by a Rees congruence. This is treated as standard
   finite-state algebraic machinery.
2. **Congruence topology.** Intersections of kernels of extensions with bounded
   complement define a descending Hausdorff countable congruence uniformity on
   `F(D)`. The paper makes its metrizability explicit.
3. **Infinite-base criterion.** If an undefined base application is iterated by
   a nontrivial unary context whose induced base orbits have uniformly bounded
   finite cardinality, then a common factorial subsequence is Cauchy in every
   bounded-complement stage but has no limit represented by a finite normal
   term.

The pointwise identity on the base is only the simplest special case of the
criterion. Constant, idempotent, and uniformly bounded periodic base dynamics
are also covered.

For a finite base, the resulting topology is exactly the ordinary profinite
topology. For an infinite base, the manuscript also gives a genuinely partial
example for which `theta_1` is equality, hence the topology is discrete and
already complete. Thus partiality alone does not force new completion points.

## Scope and terminology

The paper uses standard terminology wherever possible. Free compatible
completion, Rees congruences, finite-tree-automaton sink constructions,
congruence topologies, finite-state periodicity, and profinite completion are
background and are cited as such.

No claim about a new arithmetic convention for division by zero is made. The
natural-number example uses partial division only to supply an undefined base
application and `x -> x + 0` as an elementary special case of the context
criterion.

The exact novelty and priority of the infinite-base completion criterion remain
subject to specialist review.

## Formal verification

The repository retains the existing Lean source tree and historical Lean
namespace names so that previous verification work remains reproducible. Those
internal identifiers are not used as mathematical terminology in the paper.

The toolchain is pinned in `lean-toolchain`. The existing verification command
is:

    bash scripts/verify.sh

## Building the manuscript

The manuscript build uses pdfLaTeX and BibTeX:

    bash scripts/build-paper.sh

The generated PDF is written to:

    build/paper/Finite_Complement_Congruence_Topology_Adrian_Puha.pdf

To refresh the checked-in copy after the manuscript is finalized:

    bash scripts/build-paper.sh --update-committed

## Current branch

The active rewrite branch is:

    rewrite/paper1-standard-terminology

It is intentionally separate from `main` while the mathematical positioning,
terminology, and literature audit are still being revised.
