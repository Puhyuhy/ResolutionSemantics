#!/usr/bin/env python3
"""Static consistency checks for the current finite-complement manuscript."""

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
CITATION = ROOT / "CITATION.cff"
LAKEFILE = ROOT / "lakefile.toml"

EXPECTED_TITLE = "A Finite-Complement Congruence Topology for Partial Algebras"
EXPECTED_INPUTS = [
    "introduction",
    "free-completion",
    "finite-complement-discrimination",
    "finite-complement-completion",
    "examples",
    "conclusion",
]
BIB_FILES = [
    PAPER_DIR / "references.bib",
    PAPER_DIR / "references-completion.bib",
    PAPER_DIR / "references-separation.bib",
    PAPER_DIR / "references-standardization.bib",
]


def fail(message: str) -> None:
    print(f"manuscript check failed: {message}", file=sys.stderr)
    raise SystemExit(1)


required_files = [
    ROOT / "README.md",
    MANUSCRIPT,
    STYLE,
    CITATION,
    LAKEFILE,
    *BIB_FILES,
]
for path in required_files:
    if not path.is_file() or path.stat().st_size == 0:
        fail(f"missing or empty required file: {path.relative_to(ROOT)}")

main_tex = MANUSCRIPT.read_text(encoding="utf-8")
style = STYLE.read_text(encoding="utf-8")
citation = CITATION.read_text(encoding="utf-8")
lakefile = LAKEFILE.read_text(encoding="utf-8")

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

input_names = re.findall(r"\\input\{([^}]+)\}", main_tex)
if input_names != EXPECTED_INPUTS:
    fail("unexpected manuscript input list: " + ", ".join(input_names))
input_files = [LATEX_DIR / f"{name}.tex" for name in input_names]
for path in input_files:
    if not path.is_file() or path.stat().st_size == 0:
        fail(f"missing or empty manuscript input: {path.relative_to(ROOT)}")

tex = "\n".join([main_tex] + [p.read_text(encoding="utf-8") for p in input_files])

expected_bibliography = (
    "\\bibliography{../references,../references-completion,"
    "../references-separation,../references-standardization}"
)
if expected_bibliography not in main_tex:
    fail("unexpected bibliography list")

bib_keys: list[str] = []
for bib in BIB_FILES:
    source = bib.read_text(encoding="utf-8")
    bib_keys.extend(re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", source))
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
