#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
MODE="build"

if [[ $# -gt 1 ]]; then
  echo "usage: $0 [--check-committed|--update-committed]" >&2
  exit 2
fi
if [[ $# -eq 1 ]]; then
  case "$1" in
    --check-committed) MODE="check" ;;
    --update-committed) MODE="update" ;;
    *)
      echo "usage: $0 [--check-committed|--update-committed]" >&2
      exit 2
      ;;
  esac
fi

export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1786924800}"
export FORCE_SOURCE_DATE=1
export TZ=UTC

WORK_DIR="$(mktemp -d)"
trap 'rm -rf -- "$WORK_DIR"' EXIT

mkdir -p "$WORK_DIR/latex" "$ROOT_DIR/build/paper"
cp "$ROOT_DIR"/paper/latex/* "$WORK_DIR/latex/"
cp "$ROOT_DIR"/paper/*.bib "$WORK_DIR/"

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

OUTPUT="$ROOT_DIR/build/paper/Finite_Complement_Discrimination_Adrian_Puha.pdf"
COMMITTED="$ROOT_DIR/paper/Finite_Complement_Discrimination_Adrian_Puha.pdf"
cp paper.pdf "$OUTPUT"

PDF_INFO="$(pdfinfo "$OUTPUT")"
if ! grep -Eq '^Author:[[:space:]]+Adrian Puha[[:space:]]*$' <<<"$PDF_INFO"; then
  echo "built PDF has incorrect author metadata" >&2
  exit 1
fi
if ! grep -Fq 'Discrimination by Finite-Complement Completions of Partial Algebras' <<<"$PDF_INFO"; then
  echo "built PDF has incorrect title metadata" >&2
  exit 1
fi

pdftotext "$OUTPUT" - | grep -Fq 'Adrian Puha'

if [[ "$MODE" == "update" ]]; then
  cp "$OUTPUT" "$COMMITTED"
  echo "updated committed paper: $COMMITTED"
elif [[ "$MODE" == "check" ]]; then
  if ! cmp -s "$OUTPUT" "$COMMITTED"; then
    echo "checked-in PDF does not match the deterministic LaTeX build" >&2
    echo "run: bash scripts/build-paper.sh --update-committed" >&2
    exit 1
  fi
  echo "checked-in PDF matches the deterministic LaTeX build"
fi

echo "paper build passed: $OUTPUT"
