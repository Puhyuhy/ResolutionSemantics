#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"

export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1786924800}"
export FORCE_SOURCE_DATE=1
export TZ=UTC

WORK_DIR="$(mktemp -d)"
trap 'rm -rf -- "$WORK_DIR"' EXIT

mkdir -p "$WORK_DIR/latex" "$ROOT_DIR/build/paper"
cp "$ROOT_DIR"/paper/latex/* "$WORK_DIR/latex/"
cp "$ROOT_DIR"/paper/*.bib "$WORK_DIR/"

cd "$WORK_DIR/latex"
pdflatex -interaction=nonstopmode -halt-on-error restructured.tex
bibtex restructured
pdflatex -interaction=nonstopmode -halt-on-error restructured.tex
pdflatex -interaction=nonstopmode -halt-on-error restructured.tex

if grep -En \
    'LaTeX Warning: (Citation|Reference).*undefined|There were undefined (references|citations)|multiply defined' \
    restructured.log; then
  echo "unresolved or duplicate restructured-manuscript references found" >&2
  exit 1
fi

OUTPUT="$ROOT_DIR/build/paper/Resolution_Semantics_Restructured_Preview.pdf"
cp restructured.pdf "$OUTPUT"

PDF_INFO="$(pdfinfo "$OUTPUT")"
if ! grep -Eq '^Author:[[:space:]]+Adrian Puha[[:space:]]*$' <<<"$PDF_INFO"; then
  echo "restructured PDF has incorrect author metadata" >&2
  exit 1
fi
if ! grep -Fq 'Resolution Semantics for Partial Algebras' <<<"$PDF_INFO"; then
  echo "restructured PDF has incorrect title metadata" >&2
  exit 1
fi

pdftotext "$OUTPUT" - | grep -Fq 'Compression'
pdftotext "$OUTPUT" - | grep -Fq 'finite-pattern escape'
pdftotext "$OUTPUT" - | grep -Fq 'Adrian Puha'

echo "restructured paper preview passed: $OUTPUT"
