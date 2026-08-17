# Resolution Semantics

**Resolution Semantics for Partial Algebras: Intrinsic Finite-Complement
Separation and Observational Completion, with a Lean-Checked Many-Sorted
Encoding Bridge**

Author: **Adrian Puha**

[![Verify paper package](https://github.com/Puhyuhy/ResolutionSemantics/actions/workflows/verify.yml/badge.svg)](https://github.com/Puhyuhy/ResolutionSemantics/actions/workflows/verify.yml)

[Read the current paper](paper/Resolution_Semantics_Adrian_Puha.pdf)

This repository is the self-contained, paper-only release of the manuscript
and its Lean formalization. It intentionally excludes exploratory projects,
superseded drafts, phase reports, temporary logs, and future Strong Totality
work.

## Status

Version 1.2.0 (17 August 2026) is the specialist-review release. The Lean
development checks the stated formal results. The exact novelty and priority
of the combined mathematical package remain open specialist questions; no
historical-priority claim is made.

## Main formal results

- normalized free compatible completion of a binary partial algebra;
- quotient presentation by equality after resolution;
- intrinsic finite-complement separation over a pointwise-preserved base;
- equivalence with the canonical finite-tag presentation;
- a base-faithful finite separator and explicit whole-target bound whenever the
  old carrier is finitely coded; its ordinary residual-finiteness consequence
  is positioned against classical finite-signature ground-term recognizability;
- a proof that the old image is a total subalgebra of generated Answers exactly
  when the original evaluator is total, separating the construction from
  ordinary finite Rees index in the genuinely partial case;
- the induced separated filtration and complete observational completion;
- exact preservation and reflection of constant-bearing universal equations;
- properness iff the old evaluator is partial for finitely coded bases;
- an old-fixing-context sufficient criterion over arbitrary bases;
- a formal proof that these two properness hypotheses are incomparable, using
  the one-point algebra and natural arithmetic as opposite witnesses;
- natural- and integer-arithmetic instances with proper completions and
  unbounded finite separation ranks;
- a supporting many-sorted, arbitrary-finite-arity bridge to Diaconescu's
  total-algebra encoding, with separate `TF`/`PF` symbols, the Horn theory
  `Gamma`, the translations `alpha` and `beta`, and the satisfaction condition;
- a canonical many-sorted `gamma` construction, recovery by `beta` up to
  partial-algebra equivalence, and the unique encoded lift (persistent
  liberality), together with the functor laws, hom-set equivalence, naturality,
  unit and counit, triangle identities, semantic consequence, and both
  fixed-signature initiality transfers;
- an explicit quasi-existence syntax and conditional term-model construction
  checking the fixed-signature, operations-only initial-model conclusion used
  in Diaconescu's Corollary 4.2;
- a formal equivalence between the pre-existing binary Resolution
  implementation and the singleton-sort, no-`TF`, binary-`PF` instance of the
  many-sorted construction, including the generated data and truth carriers
  and all encoded operations.

The final four items establish provenance and exact formal compatibility with
the cited encoding. They are a machine-checked continuation of established
work, not the novelty claim of this paper.

Division by zero is represented by a structured non-old Answer. The paper does
not assign an ordinary numerical value to a/0, and it does not prove Strong
Totality.

The paper explicitly treats free completion, finite-signature ground-term
recognizability, operation-tree syntax, and standard Cauchy completion as prior
art. The open novelty question concerns the relative observer class that fixes
a possibly infinite partial base pointwise while bounding only its complement,
and the completion and properness results built from that class.

## Reproducing the formal verification

Requirements:

- Lean 4.33.0 through Elan;
- Python 3;
- a POSIX shell.

The toolchain is pinned in [lean-toolchain](lean-toolchain).

    bash scripts/verify.sh

The command builds every paper-facing Lean module, checks the manuscript/API
map, rejects proof holes, and requires every audited public theorem to depend
only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Building the paper

The PDF build requires pdfLaTeX, BibTeX, the standard LaTeX extra packages,
and Poppler utilities.

    bash scripts/build-paper.sh

The rebuilt PDF is written to
build/paper/Resolution_Semantics_Adrian_Puha.pdf.
After editing the LaTeX source, refresh the checked-in copy with

    bash scripts/build-paper.sh --update-committed

CI uses `--check-committed` to reject a PDF that does not exactly match the
deterministic build.

## Repository structure

- paper/ — final PDF, LaTeX source, and bibliography;
- lean/ — proof sources required by this manuscript;
- [THEOREM_MAP.md](THEOREM_MAP.md) — paper claims mapped to Lean declarations;
- [REVIEW_GUIDE.md](REVIEW_GUIDE.md) — focused questions for independent review;
- scripts/ — reproducible verification and paper-build commands;
- .github/workflows/verify.yml — continuous verification.

The manuscript and formalization were developed with substantial AI
assistance. Adrian Puha is responsible for the claims and is seeking
independent human mathematical review before making publication claims.
