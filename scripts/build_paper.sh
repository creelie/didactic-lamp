#!/usr/bin/env bash
# build_paper.sh -- build the paper and the release files.
#
#   dist/GurvichNaumovaConjecture_final2.pdf             the paper
#   dist/GurvichNaumovaConjecture_final2-tex.zip         LaTeX source with the figures as PNG
#   dist/GurvichNaumovaConjecture_final2-arxiv.tar.gz    the same source as an arXiv tarball
#   preprintGurvichNaumovaConjecture/GurvichNaumovaConjecture.pdf
#                                                        the paper (the only file there)
#   MasterGurvichNaumovaConjecture_masterzipfinal2.zip   every tracked file with dist/ and
#                                                        the preprint folder
#
# Needs latexmk (with pdflatex and bibtex), git, zip and tar.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
for t in latexmk zip tar git; do
  command -v "$t" >/dev/null || { echo "missing tool: $t" >&2; exit 2; }
done

NAME=GurvichNaumovaConjecture
PRE=preprint$NAME
MASTER=Master${NAME}_masterzipfinal2.zip

echo "== paper"
( cd paper && rm -f main.aux main.bbl main.blg main.fdb_latexmk main.fls main.out main.spl && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex > /dev/null )
if grep -E "Overfull|Underfull|undefined|Rerun to get" paper/main.log; then
  echo "build_paper.sh: fix the warnings above" >&2
  exit 1
fi

rm -rf dist
mkdir -p dist "$PRE"
cp paper/main.pdf "dist/${NAME}_final2.pdf"
cp paper/main.pdf "$PRE/$NAME.pdf"

STAGE="$(mktemp -d)"
trap 'rm -rf "$STAGE"' EXIT

echo "== tex zip and arXiv tarball"
SRC="$STAGE/${NAME}_final2-tex"
mkdir -p "$SRC/figures"
cp paper/main.tex paper/main.bbl paper/refs.bib paper/elsarticle.cls paper/elsarticle-num.bst "$SRC/"
cp paper/figures/*.png "$SRC/figures/"
( cd "$STAGE" && zip -qrX "${NAME}_final2-tex.zip" "${NAME}_final2-tex" )
mv "$STAGE/${NAME}_final2-tex.zip" dist/
tar -czf "dist/${NAME}_final2-arxiv.tar.gz" -C "$SRC" main.tex main.bbl refs.bib elsarticle.cls elsarticle-num.bst figures

echo "== $MASTER"
mkdir -p "$STAGE/master/Master$NAME"
git ls-files -z | grep -zvE "^(dist/|$PRE/|$MASTER\$)" \
  | while IFS= read -r -d '' f; do
      [ -e "$f" ] || continue
      mkdir -p "$STAGE/master/Master$NAME/$(dirname "$f")"
      cp -p "$f" "$STAGE/master/Master$NAME/$f"
    done
mkdir -p "$STAGE/master/Master$NAME/dist" "$STAGE/master/Master$NAME/$PRE"
cp dist/* "$STAGE/master/Master$NAME/dist/"
cp "$PRE/$NAME.pdf" "$STAGE/master/Master$NAME/$PRE/"
rm -f "$MASTER"
( cd "$STAGE/master" && zip -qrX "$ROOT/$MASTER" "Master$NAME" )

echo "built: $(ls dist | tr '\n' ' ')$PRE/$NAME.pdf $MASTER"
