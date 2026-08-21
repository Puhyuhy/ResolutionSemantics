#!/usr/bin/env python3
"""Reject missing Strong Totality v1 audit entries and unexpected axioms."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUDIT_SOURCE = ROOT / "lean" / "ResolutionStrongTotalityV1AxiomAudit.lean"
AUDIT_OUTPUT = ROOT / "build" / "v1-axiom-audit.txt"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def fail(message: str) -> None:
    print(f"Strong Totality v1 axiom audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


if not AUDIT_OUTPUT.is_file():
    fail(f"missing output: {AUDIT_OUTPUT.relative_to(ROOT)}")

source = AUDIT_SOURCE.read_text(encoding="utf-8")
output = AUDIT_OUTPUT.read_text(encoding="utf-8")
expected = set(re.findall(r"^#print\s+axioms\s+([A-Za-z0-9_'.]+)\s*$", source, re.M))
if not expected:
    fail("audit source contains no '#print axioms' declarations")

observed: dict[str, set[str]] = {}
for name, body in re.findall(
    r"'([^']+)'\s+depends on axioms:\s*\[(.*?)\]", output, re.S
):
    observed[name] = {
        item.strip()
        for item in re.split(r",\s*", body.strip())
        if item.strip()
    }
for name in re.findall(r"'([^']+)'\s+does not depend on any axioms", output):
    observed[name] = set()

missing = expected - observed.keys()
if missing:
    fail("missing theorem output: " + ", ".join(sorted(missing)))

unexpected: dict[str, set[str]] = {}
for name in expected:
    extra = observed[name] - ALLOWED_AXIOMS
    if extra:
        unexpected[name] = extra
if unexpected:
    details = "; ".join(
        f"{name}: {', '.join(sorted(axioms))}"
        for name, axioms in sorted(unexpected.items())
    )
    fail("unexpected dependencies: " + details)

print(
    f"Strong Totality v1 axiom audit passed: {len(expected)} theorems; allowed dependencies: "
    + ", ".join(sorted(ALLOWED_AXIOMS))
)
