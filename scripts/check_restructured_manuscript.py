#!/usr/bin/env python3
"""Check the branch-only restructured manuscript against the audited Lean API."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LATEX = ROOT / "paper" / "latex"
AUDIT = ROOT / "lean" / "AxiomAudit.lean"

parts = [LATEX / "restructured.tex"] + sorted(LATEX.glob("restructured-*.tex"))
missing_files = [p for p in parts if not p.is_file() or p.stat().st_size == 0]
if missing_files:
    raise SystemExit(
        "missing or empty restructured manuscript file(s): "
        + ", ".join(str(p.relative_to(ROOT)) for p in missing_files)
    )

tex = "\n".join(p.read_text(encoding="utf-8") for p in parts)
audit = AUDIT.read_text(encoding="utf-8")

lean_names = {
    name.replace(r"\_", "_")
    for name in re.findall(r"\\leanname\{([^}]+)\}", tex)
}
if not lean_names:
    raise SystemExit("restructured manuscript contains no Lean declaration links")

missing = [name for name in sorted(lean_names) if f"#check {name}" not in audit]
if missing:
    raise SystemExit(
        "restructured manuscript declaration(s) absent from AxiomAudit.lean: "
        + ", ".join(missing)
    )

required = {
    "ResolutionSemantics.MasterTheorems.relativeFinitePatternRealization",
    "ResolutionSemantics.MasterTheorems.orbitCompressionCauchy",
    "ResolutionSemantics.MasterTheorems.finitePatternEscapeNoGeneratedLimit",
    "ResolutionSemantics.MasterTheorems.compressedEscapingOrbitEmbeddingNotSurjective",
    "ResolutionSemantics.MasterTheorems.finiteBasePropernessCriterion",
    "ResolutionSemantics.MasterTheorems.oldFixingPropernessViaCombinedMaster",
    "ResolutionSemantics.MasterTheorems.oldFixingRanksUnbounded",
    "ResolutionSemantics.equationConservative",
}
missing_required = sorted(required - lean_names)
if missing_required:
    raise SystemExit(
        "restructured manuscript missing required headline declaration(s): "
        + ", ".join(missing_required)
    )

for forbidden in (
    "(n+2)!/(n+3)!",
    "c_{(n+2)!}\\stageeq{n}c_{(n+3)!}",
):
    if forbidden in tex:
        raise SystemExit(f"stale old-fixing bound remains in restructured manuscript: {forbidden}")

if "finite-pattern escape" not in tex.lower():
    raise SystemExit("restructured manuscript does not foreground finite-pattern escape")
if "trajectory compression" not in tex.lower():
    raise SystemExit("restructured manuscript does not foreground trajectory compression")

print(
    f"restructured manuscript/API check passed: {len(lean_names)} cited Lean declarations, "
    f"{len(parts)} LaTeX files"
)
