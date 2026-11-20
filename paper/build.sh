#!/bin/sh
# Build paper/main.pdf into paper/build/ (pdflatex + bibtex, bibliography in refs.bib). Run from paper/.
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass1.log
BIBINPUTS=.: bibtex build/main > build/bibtex.log
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass2.log
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build main.tex > build/pass3.log
grep -E "^Warning|error" build/main.blg || echo "bibtex: no warnings"
grep -E "^!|undefined|multiply defined" build/main.log || echo "no errors, no undefined references"
grep -c "Overfull" build/main.log || true
