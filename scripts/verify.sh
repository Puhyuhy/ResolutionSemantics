#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
cd "$ROOT_DIR"

if ! command -v lean >/dev/null 2>&1 || ! command -v lake >/dev/null 2>&1; then
  echo "Lean and Lake are required (see lean-toolchain)." >&2
  exit 1
fi

LEAN_VERSION="$(lean --version)"
case "$LEAN_VERSION" in
  *"version 4.33.0"*) ;;
  *)
    echo "expected Lean 4.33.0, got: $LEAN_VERSION" >&2
    exit 1
    ;;
esac

if grep -REn --include='*.lean' \
    '^[[:space:]]*(sorry|admit|axiom)([[:space:](]|$)|:=[[:space:]]*(sorry|admit)([[:space:]]|$)' \
    lean; then
  echo "proof hole or local axiom found in paper sources" >&2
  exit 1
fi

if grep -REn --include='*.lean' \
    'NewMath|UniversalTotality|namespace[[:space:]]+(Curvature|Omega)' lean; then
  echo "unrelated research namespace found in paper sources" >&2
  exit 1
fi

python3 scripts/check_manuscript.py
lake build Paper

mkdir -p build
lake env lean lean/AxiomAudit.lean | tee build/axiom-audit.txt
python3 scripts/check_axiom_audit.py
lake env lean lean/ResolutionStrongTotalityV1AxiomAudit.lean | tee build/v1-axiom-audit.txt
python3 scripts/check_v1_axiom_audit.py

echo "Lean build, manuscript/API check, paper axiom audit, and Strong Totality v1 axiom audit passed."
