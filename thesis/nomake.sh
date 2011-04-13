#!/bin/sh

cp szakdoli.tex latex.tex
latex latex.tex
bibtex latex.aux
latex latex.tex
latex latex.tex
dvips -t a4 -Ppdf -G0 latex.dvi
ps2pdf -dPDFSETTINGS=/printer -dUseCIEColor=true -sPAPERSIZE=a4 latex.ps

cp szakdoli.tex pdflatex.tex
pdflatex pdflatex.tex
bibtex pdflatex.aux
pdflatex pdflatex.tex
pdflatex pdflatex.tex
