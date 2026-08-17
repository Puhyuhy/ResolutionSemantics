#!/usr/bin/env python3
"""Check that the public package and manuscript-facing Lean API agree."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
MANUSCRIPT = ROOT / "paper" / "latex" / "revised.tex"
STYLE = ROOT / "paper" / "latex" / "resolution-paper.sty"
AUDIT = LEAN_DIR / "AxiomAudit.lean"
CITATION = ROOT / "CITATION.cff"
LAKEFILE = ROOT / "lakefile.toml"


def fail(message: str) -> None:
    print(f"manuscript check failed: {message}", file=sys.stderr)
    raise SystemExit(1)


required_files = [
    ROOT / "README.md",
    ROOT / "REVIEW_GUIDE.md",
    ROOT / "THEOREM_MAP.md",
    CITATION,
    ROOT / "paper" / "Resolution_Semantics_Adrian_Puha.pdf",
    MANUSCRIPT,
    STYLE,
    ROOT / "paper" / "references.bib",
    ROOT / "paper" / "references-completion.bib",
    ROOT / "paper" / "references-separation.bib",
    AUDIT,
]
for path in required_files:
    if not path.is_file() or path.stat().st_size == 0:
        fail(f"missing or empty required file: {path.relative_to(ROOT)}")

tex = MANUSCRIPT.read_text(encoding="utf-8")
style = STYLE.read_text(encoding="utf-8")
audit = AUDIT.read_text(encoding="utf-8")
citation = CITATION.read_text(encoding="utf-8")
lakefile = LAKEFILE.read_text(encoding="utf-8")
docs = "\n".join(
    (ROOT / name).read_text(encoding="utf-8")
    for name in ("README.md", "REVIEW_GUIDE.md", "THEOREM_MAP.md")
)

expected_title = (
    "Resolution Semantics for Partial Algebras: A Lean-Checked Many-Sorted "
    "Encoding Bridge and a Binary Observational Completion"
)
if "\\author{Adrian Puha}" not in tex:
    fail("the LaTeX author is not Adrian Puha")
if "pdfauthor={Adrian Puha}" not in style:
    fail("the PDF metadata author is not Adrian Puha")
if expected_title not in style:
    fail("the PDF metadata title is stale")
if "references-phase" in tex:
    fail("the manuscript still uses an internal phase bibliography name")

citation_version = re.search(r"^version:\s*([^\s]+)\s*$", citation, re.M)
lake_version = re.search(r'^version\s*=\s*"([^"]+)"\s*$', lakefile, re.M)
style_version = re.search(r"\\newcommand\{\\resolutionversion\}\{([^}]+)\}", style)
if not citation_version or not lake_version or not style_version:
    fail("could not read a package version from CFF, Lake, and manuscript style")
versions = {citation_version.group(1), lake_version.group(1), style_version.group(1)}
if len(versions) != 1:
    fail("CFF, Lake, and manuscript versions disagree: " + ", ".join(sorted(versions)))
if "Review version \\resolutionversion" not in style:
    fail("the running header does not identify the review version")

for stale in (
    "Anonymous",
    "NewMath",
    "namespace Curvature",
    "namespace Omega",
    "Relative Finite Separation",
):
    if stale in tex or stale in style or stale in docs:
        fail(f"stale project language remains: {stale}")

lean_sources = list(LEAN_DIR.glob("*.lean"))
if not lean_sources:
    fail("no Lean sources found")

local_modules = {path.stem for path in lean_sources}
for path in lean_sources:
    source = path.read_text(encoding="utf-8")
    for imported in re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", source, re.M):
        if imported.startswith("Resolution") and imported not in local_modules:
            fail(f"{path.name} imports absent local module {imported}")

lean_names = {
    name.replace(r"\_", "_")
    for name in re.findall(r"\\leanname\{([^}]+)\}", tex)
}
if not lean_names:
    fail("the manuscript contains no Lean declaration links")

for name in sorted(lean_names):
    if f"#check {name}" not in audit:
        fail(f"manuscript declaration is absent from AxiomAudit.lean: {name}")

required_headlines = {
    "ResolutionSemantics.qualitativeFiniteComplementSeparating_theorem",
    "ResolutionSemantics.ResidualComparison.finiteBaseGeneratedResiduallyFinite",
    "ResolutionSemantics.ResidualComparison.generatedOldClosedIffEvaluatorTotal",
    "ResolutionSemantics.FiniteBaseCompletion.completeIffTotal",
    "ResolutionSemantics.OldFixingContextCompletion.embeddingNotSurjective",
    "ResolutionSemantics.PropernessCriteria.onePointProperWithoutOldFixing",
    "ResolutionSemantics.PropernessCriteria.natProperWithoutFiniteCoding",
    "ResolutionSemantics.NatDivision.oldFixingCriterion",
    "ResolutionSemantics.IntDivision.completionEmbeddingNotSurjective",
}
missing = required_headlines - lean_names
if missing:
    fail("headline declarations missing from manuscript: " + ", ".join(sorted(missing)))

print(
    f"manuscript/API check passed: {len(lean_names)} cited Lean declarations, "
    f"{len(lean_sources)} proof files"
)
