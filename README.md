# A Finite-Complement Congruence Topology for Partial Algebras

Author: **Adrian Puha**

This repository contains a short manuscript on the congruence topology induced
by compatible total extensions of a partial algebra that retain the base
carrier pointwise and add only finitely many elements outside it.

The manuscript source is in `paper/latex/`, with `paper.tex` as the root.  The
Lean development is supplementary and is not required to read or verify the
paper's mathematical proofs.

## Mathematical content

Let `D` be a partial algebra with carrier `A`, and let `F(D)` be its free
compatible total extension.  A **finite-complement compatible extension** is a
compatible total algebra `T` containing the embedded copy of `A` pointwise and
satisfying `|T \ A| < infinity`.

The paper has four main components:

1. **Finite-complement separation.** A finite subterm closure is retained and
   its complement is collapsed by a Rees congruence.  The quotient map is
   injective on any prescribed finite set of generated terms.
2. **Congruence topology.** Intersections of kernels of extensions with bounded
   complement give a countable separated congruence uniformity on `F(D)`.  For
   finite `A` and finite signature, the resulting topology is exactly the
   ordinary profinite topology.
3. **Infinite-base criterion and boundary example.** A nontrivial one-hole
   context with uniformly bounded finite base orbits gives a Cauchy sequence
   whose limit is not represented in `F(D)`.  Conversely, an infinite partial
   algebra with one nowhere-defined binary operation has discrete
   finite-complement topology.
4. **Prefix-depth contrast.** An explicit comb sequence is Cauchy for the
   classical prefix-depth tree metric but not for the finite-complement
   uniformity.

The exact novelty and priority of the infinite-base criterion remain subject to
specialist review.  The manuscript treats free compatible completion, Rees
congruences, finite-tree-automaton sink constructions, congruence topologies,
finite-state periodicity, factorial synchronization, profinite completion, and
classical prefix-depth tree metrics as background.

The natural-number example uses partial division only to supply an undefined
base application.  No numerical value is assigned to `0/0`.

## Supplementary formalization

The publication-facing Lean entry point is:

```text
lean/FiniteComplementTopology.lean
```

It exposes a small interface for the formal results that directly support the
current manuscript.  The larger `lean/` tree retains earlier proof modules for
reproducibility and provenance; historical internal names are not manuscript
terminology.

See [FORMALIZATION.md](FORMALIZATION.md) for an exact account of what is and is
not machine checked, including the indexing difference between the historical
finite-tag implementation and the manuscript's complement-size convention.

To run the formal checks:

```bash
bash scripts/verify.sh
```

The toolchain is pinned in `lean-toolchain`.

## Building the manuscript

The manuscript build uses pdfLaTeX and BibTeX:

```bash
bash scripts/build-paper.sh
```

The generated PDF is written to:

```text
build/paper/Finite_Complement_Congruence_Topology_Adrian_Puha.pdf
```

Continuous integration rebuilds both the supplementary Lean target and the PDF
from source.
