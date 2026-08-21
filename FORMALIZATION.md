# Supplementary Lean formalization

The manuscript **A Finite-Complement Congruence Topology for Partial Algebras**
is self-contained.  The Lean development is supplementary: it checks several
constructions and special cases used in the mathematical argument, but it is
not presented as a line-by-line formalization of the current paper.

The publication-facing entry point is:

```text
lean/FiniteComplementTopology.lean
```

That module deliberately exposes a small interface with terminology close to
the manuscript.  The larger `lean/` directory contains the earlier development
from which these results were extracted; historical module and declaration
names are retained so that existing proofs and their provenance remain
reproducible.  The full retained module graph is still compiled in CI, while
`FiniteComplementTopology.lean` is the interface intended for readers of the
current paper.

## What is checked

The facade exposes machine-checked results for:

| Manuscript component | Lean declaration |
| --- | --- |
| Universal property of the free compatible total extension | `FiniteComplementTopology.freeCompatibleExtensionUniversal` |
| Qualitative finite-complement separation | `FiniteComplementTopology.finiteComplementSeparation` |
| Embedded base closed under the generated total operations iff the partial algebra is total | `FiniteComplementTopology.baseClosedIffTotal` |
| Pointwise-fixed-context special case of the incompleteness criterion | `FiniteComplementTopology.pointwiseFixedContextGivesProperCompletion` |
| Natural-number `0/0`, `x + 0` special case | `FiniteComplementTopology.naturalNumbersExampleGivesProperCompletion` |
| Prefix-depth Cauchy sequence that is not Cauchy for finite-complement observation | `FiniteComplementTopology.prefixDepthCauchyNotFiniteComplementCauchy` |

The proof files also contain lower-level lemmas for the generated term model,
finite-state orbit arguments, finite-complement presentations, and the explicit
comb construction.

## What is not claimed to be formalized exactly

Two current manuscript statements are proved directly in the paper but are not
exposed as exact Lean theorems in the supplementary facade:

1. the generalized infinite-base criterion for a one-hole context whose base
   orbits have uniformly bounded finite cardinality;
2. the discrete infinite-base example with one nowhere-defined binary
   operation.

The formal pointwise-fixed-context theorem is a genuine special case of the
first statement, not a substitute for its full generality.

## Finite-tag implementation versus complement size

Some historical proof modules use carriers of the form

```text
A + (Fin n + Unit)
```

and call `n` the number of finite tags.  Such a carrier has `n + 1` points
outside the embedded base because the `Unit` summand is an overflow state.
Consequently the one-tag comb observer in `ResolutionCompletionProbe.lean`
has **two** external points in the manuscript's current complement-size
convention.  The paper therefore states the prefix-depth contrast directly
with two new points `p` and `q`, i.e. at `theta_2`.

This is an indexing/presentation difference only.  As the budget ranges over
all finite values, the historical finite-tag filtration and the bounded
finite-complement viewpoint describe the same qualitative finite-complement
separation mechanism used by the checked special cases.

## Reproducing the checks

The toolchain is pinned by `lean-toolchain` to Lean 4.33.0.  Run:

```bash
bash scripts/verify.sh
```

The command:

1. rejects `sorry`, `admit`, and local `axiom` declarations in the Lean tree;
2. runs the static manuscript/repository consistency checker;
3. builds the full retained Lean library, including the publication-facing
   facade;
4. evaluates `lean/AxiomAudit.lean` on the facade declarations;
5. rejects axiom dependencies outside `propext`, `Classical.choice`, and
   `Quot.sound`.

The mathematical manuscript does not require the repository or Lean in order
to be read or assessed.
