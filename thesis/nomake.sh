#!/bin/sh

cp szakdoli.tex latex.tex
latex latex.tex
bibtex latex.aux
latex latex.tex
latex latex.tex
dvips -t a4 -Ppdf -G0 latex.dvi
ps2pdf -dPDFSETTINGS=/printer -dUseCIEColor=true -sPAPERSIZE=a4 latex.ps
rm -f latex.aux
rm -f latex.log
rm -f latex.out
rm -f latex.bbl
rm -f latex.blg
rm -f latex.toc
rm -f latex.tdo
rm -f latex.tex

cp szakdoli.tex pdflatex.tex
pdflatex pdflatex.tex
bibtex pdflatex.aux
pdflatex pdflatex.tex
pdflatex pdflatex.tex
rm -f pdflatex.aux
rm -f pdflatex.log
rm -f pdflatex.out
rm -f pdflatex.bbl
rm -f pdflatex.blg
rm -f pdflatex.toc
rm -f pdflatex.tdo
rm -f pdflatex.tex
