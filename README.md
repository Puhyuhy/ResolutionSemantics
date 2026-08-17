# Resolution Semantics

**Resolution Semantics for Partial Algebras: Intrinsic Finite-Complement
Separation and Observational Completion, with a Lean-Checked Many-Sorted
Encoding Bridge**

Author: **Adrian Puha**

[![Verify paper package](https://github.com/Puhyuhy/ResolutionSemantics/actions/workflows/verify.yml/badge.svg)](https://github.com/Puhyuhy/ResolutionSemantics/actions/workflows/verify.yml)

[Read the current paper](paper/Resolution_Semantics_Adrian_Puha.pdf)

This repository is the self-contained paper and Lean formalization package.
It intentionally excludes exploratory projects, superseded phase reports,
temporary logs, and future Strong Totality work.

## Status

Version 1.2.0, manuscript revision dated 18 August 2026, is under specialist
review. The Lean development checks the stated formal results. The exact
novelty and priority of the combined mathematical package remain open
specialist questions; no historical-priority claim is made.

## Structural result architecture

The promoted manuscript is organized around two master principles and one
Resolution-specific anti-limit mechanism.

1. **Master I — relative finite-pattern realization.** For every finite family
   of generated Answers, one compatible finite-complement observer fixes the
   entire partial base pointwise and is simultaneously injective on that
   family. Pairwise finite-tag separation is the two-point consequence; the
   explicit constructor-size pair bound is retained.
2. **Master II — trajectory compression.** At each finite observation stage it
   is enough for the single deterministic trajectory relevant to a chosen
   generated unary family to admit a finite code. The whole observer carrier
   need not be finite. Standard periodicity and factorial divisibility then
   make the factorial sample Cauchy.
3. **Finite-pattern escape.** For a syntactically growing unary orbit, a
   candidate-tailored finite-pattern observer realizes the candidate and a
   long orbit prefix exactly, sends the next unseen iterate to absorbing
   overflow, and thereby rules out every generated candidate as a limit.
4. **Combined properness theorem.** Trajectory compression plus finite-pattern
   escape yields a Cauchy sequence with no generated limit, hence a proper
   observational completion.

The finite-base criterion and the arbitrary-base old-fixing theorem are
formally checked instances of this same combined mechanism. In the old-fixing
case the sharp stage-`n` witness is

`c_(n+1)! ~_n c_(n+2)!`,

which gives unbounded finite separation ranks.

## Other main formal results

- normalized free compatible completion of a binary partial algebra and its
  quotient presentation by equality after resolution;
- intrinsic finite-complement observers over a pointwise-preserved, possibly
  infinite partial base, with equivalence to canonical finite-tag models;
- the induced separated filtration and complete observational completion;
- exact preservation and reflection of constant-bearing universal equations;
- for finitely coded bases, properness exactly when some base application is
  undefined;
- over arbitrary bases, the old-fixing-context instance of the combined
  compression–escape theorem;
- natural- and integer-arithmetic instances using the undefined seed `0/0` and
  the context `x ↦ x + 0`;
- a supporting many-sorted, arbitrary-finite-arity formalization of the
  operations-only fragment of Diaconescu's encoding, including satisfaction,
  recovery, persistent liberality, adjunction laws, semantic consequence,
  fixed-signature initiality transfers, and the binary specialization bridge.

The Diaconescu development establishes provenance and exact formal
compatibility with established partial-to-total infrastructure. It is not a
separate novelty claim of this paper.

Division by zero is represented by a structured non-old Answer. The paper does
not assign an ordinary numerical value to `a/0`, and it does not prove Strong
Totality.

## Novelty discipline

The paper explicitly treats the following as background rather than novelty:
free compatible completion, finite selected-subterm/sink constructions in
isolation, finite-state eventual periodicity, factorial synchronization,
generic Cauchy completion, and Diaconescu's encoding itself.

The strongest contribution under review is the interaction of a pointwise-
preserved possibly infinite partial base, finite complexity only outside that
base, simultaneous finite-pattern realization, trajectory-level compression,
and finite-pattern escape witnesses that force proper observational
completions.

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
`build/paper/Resolution_Semantics_Adrian_Puha.pdf`.
After editing the LaTeX source, refresh the checked-in copy with

    bash scripts/build-paper.sh --update-committed

CI uses `--check-committed` to reject a PDF that does not exactly match the
deterministic build.

## Repository structure

- `paper/` — committed PDF, LaTeX source, and bibliography;
- `lean/` — proof sources required by the manuscript;
- [`THEOREM_MAP.md`](THEOREM_MAP.md) — structural claims mapped to Lean declarations;
- [`REVIEW_GUIDE.md`](REVIEW_GUIDE.md) — focused questions for independent review;
- [`MASTER_THEOREMS.md`](MASTER_THEOREMS.md) — research reduction behind the promoted architecture;
- `scripts/` — reproducible verification and paper-build commands;
- `.github/workflows/verify.yml` — continuous verification.

The manuscript and formalization were developed with substantial AI
assistance. Adrian Puha is responsible for the claims and is seeking
independent human mathematical review before making publication claims.
