#!/usr/bin/env python3
"""Static consistency checks for the submission-facing manuscript package."""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
PAPER_DIR = ROOT / "paper"
LATEX_DIR = PAPER_DIR / "latex"
MANUSCRIPT = LATEX_DIR / "paper.tex"
STYLE = LATEX_DIR / "paper-style.sty"
BIBLIOGRAPHY = PAPER_DIR / "references.bib"
CITATION = ROOT / "CITATION.cff"
LAKEFILE = ROOT / "lakefile.toml"
README = ROOT / "README.md"
FORMALIZATION = ROOT / "FORMALIZATION.md"
LEAN_FACADE = LEAN_DIR / "FiniteComplementTopology.lean"
AUDIT = LEAN_DIR / "AxiomAudit.lean"

EXPECTED_TITLE = "A Finite-Complement Congruence Topology for Partial Algebras"
EXPECTED_INPUTS = [
    "introduction",
    "free-completion",
    "finite-complement-discrimination",
    "finite-complement-completion",
    "conclusion",
]


def fail(message: str) -> None:
    print(f"manuscript check failed: {message}", file=sys.stderr)
    raise SystemExit(1)


required_files = [
    README,
    FORMALIZATION,
    MANUSCRIPT,
    STYLE,
    BIBLIOGRAPHY,
    CITATION,
    LAKEFILE,
    LEAN_FACADE,
    AUDIT,
]
for path in required_files:
    if not path.is_file() or path.stat().st_size == 0:
        fail(f"missing or empty required file: {path.relative_to(ROOT)}")

main_tex = MANUSCRIPT.read_text(encoding="utf-8")
style = STYLE.read_text(encoding="utf-8")
citation = CITATION.read_text(encoding="utf-8")
lakefile = LAKEFILE.read_text(encoding="utf-8")
readme = README.read_text(encoding="utf-8")
formalization = FORMALIZATION.read_text(encoding="utf-8")

if f"\\title{{\\textbf{{{EXPECTED_TITLE}}}}}" not in main_tex:
    fail("manuscript title is stale or unexpected")
if "\\author{Adrian Puha}" not in main_tex:
    fail("the LaTeX author is not Adrian Puha")
if f"pdftitle={{{EXPECTED_TITLE}}}" not in style:
    fail("PDF title metadata is stale")
if "pdfauthor={Adrian Puha}" not in style:
    fail("PDF author metadata is stale")
if EXPECTED_TITLE not in citation:
    fail("CITATION.cff does not name the current paper")
if EXPECTED_TITLE not in readme:
    fail("README does not name the current paper")
if "rewrite/paper1-standard-terminology" in readme or "## Current branch" in readme:
    fail("README still describes the pre-merge branch state")
if "lean/FiniteComplementTopology.lean" not in formalization:
    fail("formalization guide does not identify the public Lean entry point")

input_names = re.findall(r"\\input\{([^}]+)\}", main_tex)
if input_names != EXPECTED_INPUTS:
    fail("unexpected manuscript input list: " + ", ".join(input_names))
input_files = [LATEX_DIR / f"{name}.tex" for name in input_names]
for path in input_files:
    if not path.is_file() or path.stat().st_size == 0:
        fail(f"missing or empty manuscript input: {path.relative_to(ROOT)}")

tex = "\n".join([main_tex] + [p.read_text(encoding="utf-8") for p in input_files])

if "\\bibliography{../references}" not in main_tex:
    fail("manuscript does not use the consolidated bibliography")

bib_source = BIBLIOGRAPHY.read_text(encoding="utf-8")
bib_keys = re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", bib_source)
duplicates = sorted(k for k, count in Counter(bib_keys).items() if count > 1)
if duplicates:
    fail("duplicate bibliography keys: " + ", ".join(duplicates))
known_bib = set(bib_keys)

cited: set[str] = set()
for group in re.findall(r"\\cite[a-zA-Z]*\s*\{([^}]+)\}", tex):
    cited.update(k.strip() for k in group.split(",") if k.strip())
missing_citations = sorted(cited - known_bib)
if missing_citations:
    fail("citation keys absent from bibliography: " + ", ".join(missing_citations))
unused_bib = sorted(known_bib - cited)
if unused_bib:
    fail("uncited bibliography entries remain: " + ", ".join(unused_bib))

labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
refs: set[str] = set()
for group in re.findall(r"\\(?:[cC]ref|ref|eqref)\s*\{([^}]+)\}", tex):
    refs.update(k.strip() for k in group.split(",") if k.strip())
missing_labels = sorted(refs - labels)
if missing_labels:
    fail("cross-reference labels absent from manuscript: " + ", ".join(missing_labels))

for stale in (
    "Resolution Semantics for Partial Algebras: Intrinsic Finite-Complement",
    "finite-pattern realization",
    "trajectory compression",
    "Compression--escape properness",
    r"\leanname{",
):
    if stale.lower() in tex.lower():
        fail(f"stale manuscript language remains: {stale}")

citation_version = re.search(r"^version:\s*([^\s]+)\s*$", citation, re.M)
lake_version = re.search(r'^version\s*=\s*"([^"]+)"\s*$', lakefile, re.M)
if not citation_version or not lake_version:
    fail("could not read package version from CFF and Lake")
if citation_version.group(1) != lake_version.group(1):
    fail(
        "CFF and Lake versions disagree: "
        f"{citation_version.group(1)} vs {lake_version.group(1)}"
    )
if '"FiniteComplementTopology"' not in lakefile:
    fail("Lake roots do not include the publication-facing Lean facade")

lean_sources = list(LEAN_DIR.glob("*.lean"))
if not lean_sources:
    fail("no Lean sources found")
local_modules = {path.stem for path in lean_sources}
for path in lean_sources:
    source = path.read_text(encoding="utf-8")
    for imported in re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", source, re.M):
        if imported.startswith("Resolution") and imported not in local_modules:
            fail(f"{path.name} imports absent local module {imported}")

print(
    "manuscript consistency check passed: "
    f"{len(input_files)} sections, {len(cited)} cited bibliography keys, "
    f"{len(labels)} labels, {len(lean_sources)} supplementary Lean files"
)
