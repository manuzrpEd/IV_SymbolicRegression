#!/usr/bin/env bash
# Builds paper/main.pdf: pdflatex, bibtex, pdflatex twice. Run from anywhere:  bash paper/build.sh
set -e
cd "$(dirname "$0")"
MIKTEX="${LOCALAPPDATA:-}/Programs/MiKTeX/miktex/bin/x64"
[ -x "$MIKTEX/pdflatex.exe" ] && export PATH="$MIKTEX:$PATH"
pdflatex -interaction=nonstopmode -halt-on-error main.tex > build.log
bibtex main >> build.log
pdflatex -interaction=nonstopmode -halt-on-error main.tex >> build.log
pdflatex -interaction=nonstopmode -halt-on-error main.tex >> build.log
pdflatex -interaction=nonstopmode -halt-on-error main.tex >> build.log
echo "built main.pdf"
