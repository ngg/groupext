#!/bin/sh

latex szakdoli.tex
bibtex szakdoli.aux
latex szakdoli.tex
latex szakdoli.tex
rm -f szakdoli.aux
rm -f szakdoli.log
rm -f szakdoli.out
rm -f szakdoli.bbl
rm -f szakdoli.blg
rm -f szakdoli.toc
rm -f szakdoli.tdo

dvips -t a4 -Ppdf -G0 szakdoli.dvi

ps2pdf -dPDFSETTINGS=/printer -dUseCIEColor=true -sPAPERSIZE=a4 szakdoli.ps
