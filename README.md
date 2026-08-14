# Resolution Semantics

**Resolution Semantics for Binary Partial Algebras: A Formalized Free
Completion, Intrinsic Finite-Complement Separation, and Observational
Completion**

Author: **Adrian Puha**

[Read the current paper](paper/Resolution_Semantics_Adrian_Puha.pdf)

This repository is the self-contained, paper-only release of the manuscript
and its Lean formalization. It intentionally excludes exploratory projects,
superseded drafts, phase reports, temporary logs, and future Strong Totality
work.

## Status

This is a working preprint for independent specialist review. The Lean
development checks the stated formal results. The exact novelty and priority
of the combined mathematical package remain open specialist questions; no
historical-priority claim is made.

## Main formal results

- normalized free compatible completion of a binary partial algebra;
- quotient presentation by equality after resolution;
- intrinsic finite-complement separation over a pointwise-preserved base;
- equivalence with the canonical finite-tag presentation;
- ordinary residual finiteness, with an explicit whole-target bound, whenever
  the old carrier is finitely coded;
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
  unbounded finite separation ranks.

Division by zero is represented by a structured non-old Answer. The paper does
not assign an ordinary numerical value to a/0, and it does not prove Strong
Totality.

## Reproducing the formal verification

Requirements:

- Lean 4.33.0 through Elan;
- Python 3;
- a POSIX shell.

The toolchain is pinned in [lean-toolchain](lean-toolchain).

    bash scripts/verify.sh

The command builds every paper-facing Lean module, checks the manuscript/API
map, rejects proof holes, and audits the public theorems for unexpected
sorryAx dependencies.

## Building the paper

The PDF build requires pdfLaTeX, BibTeX, the standard LaTeX extra packages,
and Poppler utilities.

    bash scripts/build-paper.sh

The rebuilt PDF is written to
build/paper/Resolution_Semantics_Adrian_Puha.pdf.

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
