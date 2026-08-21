#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

if [[ $# -ne 0 ]]; then
  echo "usage: $0" >&2
  exit 2
fi

export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1786924800}"
export FORCE_SOURCE_DATE=1
export TZ=UTC

WORK_DIR="$(mktemp -d)"
trap 'rm -rf -- "$WORK_DIR"' EXIT

mkdir -p "$WORK_DIR/latex" "$ROOT_DIR/build/paper"
cp "$ROOT_DIR"/paper/latex/* "$WORK_DIR/latex/"
cp "$ROOT_DIR"/paper/references.bib "$WORK_DIR/"

cd "$WORK_DIR/latex"
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
bibtex paper
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex

if grep -En \
    'LaTeX Warning: (Citation|Reference).*undefined|There were undefined (references|citations)|multiply defined' \
    paper.log; then
  echo "unresolved or duplicate manuscript references found" >&2
  exit 1
fi

OUTPUT="$ROOT_DIR/build/paper/Finite_Complement_Congruence_Topology_Adrian_Puha.pdf"
cp paper.pdf "$OUTPUT"

PDF_INFO="$(pdfinfo "$OUTPUT")"
if ! grep -Eq '^Author:[[:space:]]+Adrian Puha[[:space:]]*$' <<<"$PDF_INFO"; then
  echo "built PDF has incorrect author metadata" >&2
  exit 1
fi
if ! grep -Fq 'A Finite-Complement Congruence Topology for Partial Algebras' <<<"$PDF_INFO"; then
  echo "built PDF has incorrect title metadata" >&2
  exit 1
fi

pdftotext "$OUTPUT" - | grep -Fq 'Adrian Puha'

echo "paper build passed: $OUTPUT"
