#!/usr/bin/env bash
# Compiles the four TikZ figures and writes them as PNG (200 dpi) to paper/figures/.
set -euo pipefail
cd "$(dirname "$0")"
for t in pdflatex pdftoppm; do
  command -v "$t" >/dev/null || { echo "missing tool: $t" >&2; exit 2; }
done
mkdir -p ../paper/figures
for f in fig_cases fig_assembly fig_sigma fig_example; do
  pdflatex -interaction=nonstopmode -halt-on-error "$f.tex" >/dev/null
  pdftoppm -r 200 -png -singlefile "$f.pdf" "../paper/figures/$f"
done
rm -f ./*.aux ./*.log
echo "figures written to paper/figures/"
