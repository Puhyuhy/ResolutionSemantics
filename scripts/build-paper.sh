#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf -- "$WORK_DIR"' EXIT

mkdir -p "$WORK_DIR/latex" "$ROOT_DIR/build/paper"
cp "$ROOT_DIR"/paper/latex/* "$WORK_DIR/latex/"
cp "$ROOT_DIR"/paper/*.bib "$WORK_DIR/"

cd "$WORK_DIR/latex"
pdflatex -interaction=nonstopmode -halt-on-error revised.tex
bibtex revised
pdflatex -interaction=nonstopmode -halt-on-error revised.tex
pdflatex -interaction=nonstopmode -halt-on-error revised.tex

if rg -n \
    'LaTeX Warning: (Citation|Reference).*undefined|There were undefined (references|citations)|multiply defined' \
    revised.log; then
  echo "unresolved or duplicate manuscript references found" >&2
  exit 1
fi

OUTPUT="$ROOT_DIR/build/paper/Resolution_Semantics_Adrian_Puha.pdf"
cp revised.pdf "$OUTPUT"

PDF_INFO="$(pdfinfo "$OUTPUT")"
if ! grep -Eq '^Author:[[:space:]]+Adrian Puha[[:space:]]*$' <<<"$PDF_INFO"; then
  echo "built PDF has incorrect author metadata" >&2
  exit 1
fi
if ! grep -Fq 'Resolution Semantics for Binary Partial Algebras' <<<"$PDF_INFO"; then
  echo "built PDF has incorrect title metadata" >&2
  exit 1
fi

pdftotext "$OUTPUT" - | grep -Fq 'Adrian Puha'
echo "paper build passed: $OUTPUT"
