# A Finite-Complement Congruence Topology for Partial Algebras

Author: **Adrian Puha**

This branch contains a short manuscript about a congruence topology induced by
compatible total extensions of a partial algebra that retain the original
carrier pointwise and add only finitely many elements outside it.

The mathematical paper is under `paper/latex/`, with `paper.tex` as the root.
The accompanying Lean development is supplementary verification and is not
needed to read or check the proofs in the manuscript.

## Mathematical content

Let `D` be a partial algebra with carrier `A`, and let `F(D)` denote its free
compatible total extension.

A **finite-complement compatible extension** is a compatible total algebra `T`
that contains `A` pointwise and satisfies `|T \ A| < infinity`.

The manuscript has four main components:

1. **Finite separation.** A finite subterm closure is retained and its
   complement is collapsed by a Rees congruence. This is treated as standard
   finite-state algebraic machinery.
2. **Congruence topology.** Intersections of kernels of extensions with bounded
   complement define a descending Hausdorff countable congruence uniformity on
   `F(D)`. The paper makes its metrizability explicit. For a finite base this is
   exactly the ordinary profinite topology.
3. **Infinite-base criterion and boundary example.** If an undefined base
   application is iterated by a nontrivial unary context whose induced base
   orbits have uniformly bounded finite cardinality, then a common factorial
   subsequence is Cauchy in every bounded-complement stage but has no limit
   represented by a finite normal term. Conversely, an infinite genuinely
   partial example is given for which `theta_1` is equality and the topology is
   discrete and already complete.
4. **Prefix-depth contrast.** A comb sequence is Cauchy for classical
   prefix-depth agreement on trees but is separated at a fixed
   finite-complement stage, showing that the two uniformities are different.

The pointwise identity on the base is only the simplest special case of the
criterion. Constant, idempotent, and uniformly bounded periodic base dynamics
are also covered.

## Scope and terminology

The paper uses standard terminology wherever possible. Free compatible
completion, Rees congruences, finite-tree-automaton sink constructions,
congruence topologies, finite-state periodicity, profinite completion, and
classical prefix-depth tree metrics are background and are cited as such.

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
The formal tree includes underlying constructions, special cases, comparison
results, and the prefix-depth contrast; the manuscript itself is self-contained
and does not claim a one-to-one Lean declaration for every current sentence.

The toolchain is pinned in `lean-toolchain`. The verification command is:

    bash scripts/verify.sh

The static manuscript checker invoked by that command is aligned with the
current paper and verifies source structure, bibliography keys, cross-reference
keys, metadata, package versions, and local Lean imports.

## Building the manuscript

The manuscript build uses pdfLaTeX and BibTeX:

    bash scripts/build-paper.sh

The generated PDF is written to:

    build/paper/Finite_Complement_Congruence_Topology_Adrian_Puha.pdf

A checked-in PDF is optional; to create or refresh one locally after the
manuscript is finalized:

    bash scripts/build-paper.sh --update-committed

Continuous integration builds the PDF from source and preserves it as a workflow
artifact rather than requiring a committed binary to match the source tree.

## Current branch

The active manuscript branch is:

    rewrite/paper1-standard-terminology

It remains intentionally separate from `main` until an explicit merge is
authorized.
