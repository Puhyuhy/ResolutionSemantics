# Algebra Universalis submission package

Target journal: **Algebra Universalis** (Springer Nature)

Prepared from `main` merge commit `8f23bed8d02c77fb97db9a46b018b4e6485b49c0`.

## Contents

- `manuscript.tex` — single-file journal submission source using `\documentclass{birkau}`; the bibliography is embedded with `thebibliography` so the manuscript does not depend on a separate `.bib` file at upload time.
- `COVER_LETTER.md` — concise cover letter draft for the submission portal.

The mathematical statements and proofs are unchanged from the submission-ready manuscript on `main`. This branch only repackages the paper for the journal and adds required declarations/metadata.

## Journal-specific requirements addressed

- Uses the current Algebra Universalis LaTeX class name `birkau`.
- Keeps the manuscript in a single `.tex` file.
- Includes abstract and keywords.
- Includes 2020 Mathematics Subject Classification codes.
- Includes declarations for ethical approval, competing interests, authors' contributions, availability of data/materials, and funding.
- Includes a transparent acknowledgement of generative-AI assistance in accordance with Springer Nature policy.
- Points to the public Lean 4 formalization and source repository.

## Before uploading

1. Download the current official Algebra Universalis author package from the journal's Submission Guidelines page and place the supplied `birkau.cls` (and any other files required by that package) alongside `manuscript.tex` for the final journal-format compile.
2. Compile `manuscript.tex` with the **official** `birkau.cls`. A local syntax-only dry run was performed with an `amsart` shim because the journal's Google Drive template archive could not be fetched from the execution environment. The shim is deliberately **not committed** to this branch.
3. Visually inspect the resulting journal-formatted PDF after the official class is applied.
4. In the submission portal, enter the author's current email address and ORCID if applicable. These were not guessed or inserted into the source.
5. Confirm whether the portal requests a separate source-code/materials link; if so use: https://github.com/Puhyuhy/ResolutionSemantics
6. Upload any supplementary Lean material only if requested by the portal/editor; the paper itself is self-contained.

## Suggested submission metadata

**Title:** A Finite-Complement Congruence Topology for Partial Algebras

**Author:** Adrian Puha

**Affiliation:** Independent researcher

**Keywords:** partial algebra; free completion; Rees congruence; congruence topology; profinite topology

**MSC 2020:** Primary 08A55; Secondary 08A30, 08B20

## Scope of the final pre-submission check

Only journal-format compatibility should be changed at this stage. Do not reopen theorem statements, proofs, or novelty positioning unless the editor/referee raises a concrete mathematical issue.
