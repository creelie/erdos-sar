#!/bin/sh
# Build the arXiv source package paper/arxiv.tar.gz and compile it once from a clean folder.
# The package holds paper.tex, the TikZ and PNG figures and the generated tables; the Lean
# proof goes in anc/, which arXiv offers as ancillary files and does not compile.
# Run from anywhere:  sh paper/make_arxiv.sh
set -e
PAPER=$(cd "$(dirname "$0")" && pwd)
ROOT=$(dirname "$PAPER")
STAGE=$(mktemp -d)
mkdir -p "$STAGE/figures" "$STAGE/tables" "$STAGE/anc/scripts"
cp "$PAPER/paper.tex" "$STAGE/"
cp "$PAPER"/figures/fig_*.tex "$PAPER"/figures/*.png "$STAGE/figures/"
cp "$PAPER"/tables/*.tex "$STAGE/tables/"
cp -r "$ROOT/ErdosSar" "$STAGE/anc/"
cp "$ROOT/ErdosSar.lean" "$ROOT/lakefile.toml" "$ROOT/lake-manifest.json" \
   "$ROOT/lean-toolchain" "$ROOT/LICENSE" "$STAGE/anc/"
cp "$ROOT/scripts/Axioms.lean" "$STAGE/anc/scripts/"
cat > "$STAGE/anc/README.txt" <<'TXT'
Lean 4 proof of Theorem 1.1 (theorem ErdosSar.question1 in ErdosSar/Closure.lean).
Toolchain: Lean 4.34.1 with Mathlib v4.34.1 (see lean-toolchain and lakefile.toml).

  lake exe cache get
  lake build
  lake env lean scripts/Axioms.lean

The last command prints the axioms of the main results; each line reports only
[propext, Classical.choice, Quot.sound].
Repository: https://github.com/creelie/erdos-sar
Archive:    https://doi.org/10.5281/zenodo.23151794
TXT
rm -f "$PAPER/arxiv.tar.gz"
tar czf "$PAPER/arxiv.tar.gz" -C "$STAGE" paper.tex figures tables anc
rm -rf "$STAGE"

TEST=$(mktemp -d)
tar xzf "$PAPER/arxiv.tar.gz" -C "$TEST"
(cd "$TEST" && for i in 1 2 3; do pdflatex -interaction=nonstopmode -halt-on-error paper.tex > /dev/null; done)
if grep -q "undefined\|Overfull" "$TEST/paper.log"; then
  echo "warnings in the test build:"; grep "undefined\|Overfull" "$TEST/paper.log"; exit 1
fi
echo "arxiv.tar.gz: $(du -h "$PAPER/arxiv.tar.gz" | cut -f1), test build $(pdfinfo "$TEST/paper.pdf" | sed -n 's/^Pages: *//p') pages"
rm -rf "$TEST"
