# Finite-Complement Congruence Topologies for Partial Algebras

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

1. **Finite separation.** For a finite set of normal terms, retain its finite
   subterm closure and collapse the complement by a Rees congruence. The
   resulting quotient fixes the base and separates the selected terms. This is
   treated as standard finite-state algebraic machinery.
2. **Congruence topology.** Intersections of kernels of extensions with bounded
   complement define a descending Hausdorff family of congruences on `F(D)`.
3. **Infinite-base criterion.** When the retained base may be infinite, a
   nontrivial unary context that acts as the identity on every base element can
   constrain an iterated non-base term to finitely many effective states in
   every bounded-complement extension. A common factorial subsequence is then
   Cauchy, while a Rees quotient excludes every finite normal term as its limit.

For a finite base, the resulting topology is shown to be exactly the ordinary
profinite topology. The manuscript therefore treats the infinite-base case as
the part requiring separate analysis.

## Scope and terminology

The paper uses standard terminology wherever possible. Free compatible
completion, Rees congruences, finite-tree-automaton sink constructions,
congruence topologies, finite-state periodicity, and profinite completion are
background and are cited as such.

No claim about a new arithmetic convention for division by zero is made. The
natural-number example uses partial division only to supply an undefined base
application, and uses `x -> x + 0` as a base-fixing context.

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

    build/paper/Finite_Complement_Congruence_Topologies_Adrian_Puha.pdf

To refresh the checked-in copy after the manuscript is finalized:

    bash scripts/build-paper.sh --update-committed

## Current branch

The active rewrite branch is:

    rewrite/paper1-standard-terminology

It is intentionally separate from `main` while the mathematical positioning,
terminology, and literature audit are still being revised.
