# Official `birkau.cls` validation

Validated on 21 August 2026 against the official June 2026 Algebra Universalis author package supplied by the author.

Official `birkau.cls` SHA-256:

`d42080d2c966b5f413a0f363ae8211cf4a5a4ce94d4402354cdc836b126e8793`

## Build result

After applying the formatting-only patch in `AU_OFFICIAL_TEMPLATE_FIXES.patch`, the manuscript was compiled with the official `birkau.cls` using two `pdflatex` passes.

Result:
- 11 pages;
- no LaTeX warnings;
- no undefined references;
- no overfull boxes;
- no underfull boxes;
- PDF preflight passed (openable, unencrypted, text-based).

The bibliography is embedded with `thebibliography` (16 `\bibitem`s), so `spmpsci.bst` is not needed for this submission source.

## Important correction to the earlier static audit

The official `AUsample.tex` states that sole-authored papers use `\author[short]{full}`. `\corrauthor` is used to mark the corresponding author in multiple-authored papers. Therefore the sole-author manuscript should remain an `\author`, not be changed to `\corrauthor`.

## Formatting issues found only by the real class

The real class exposed one substantive formatting bug that static inspection missed: `\subjclass[2020]{...}` is not supported by this `birkau.cls` and renders incorrectly. The correct source form is:

```tex
\subjclass{08A55, 08A30, 08B20}
```

The official sample also requests sentence-case titles, a short author form, and capitalized keyword phrases. The patch records those changes together with minor line-wrap and back-matter formatting cleanup. No mathematical result is changed.

## Remaining author-supplied metadata

`AUsample.tex` asks each author to provide an address and e-mail address. The current source has only `\address{Independent researcher}`. Before final upload, add the postal address and public e-mail address that the author wants to publish.
