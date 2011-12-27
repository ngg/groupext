NAME = szakdoli
ifndef PDFLATEX
PDFLATEX = 0
endif


.PHONY: all
all: $(NAME).pdf prezentacio.pdf

ifeq ($(PDFLATEX),1)
$(NAME).pdf: pdflatex.pdf
	cp $< $@
prezentacio.pdf: prezentacio-pdflatex.pdf
	cp $< $@
else
$(NAME).pdf: latex.pdf
	cp $< $@
prezentacio.pdf: prezentacio-latex.pdf
	cp $< $@
endif

.PHONY: both
both: $(NAME).pdf prezentacio.pdf latex.pdf pdflatex.pdf prezentacio-latex.pdf prezentacio-pdflatex.pdf

DEPENDSON = szakdoli.tex bevezetes.tex blackbox.tex permutacio.tex burnside.tex mathematica.tex elte_cimer_ff.eps ref.bib thesis.cls ../GroupExt/GroupExt/GroupExt.m

pdflatex.pdf: $(DEPENDSON)
	cp $(NAME).tex pdflatex.tex
	pdflatex --shell-escape pdflatex.tex
	bibtex pdflatex.aux
	pdflatex --shell-escape pdflatex.tex
	pdflatex --shell-escape pdflatex.tex
	rm -f pdflatex.aux
	rm -f pdflatex.log
	rm -f pdflatex.out
	rm -f pdflatex.bbl
	rm -f pdflatex.blg
	rm -f pdflatex.toc
	rm -f pdflatex.tdo
	rm -f pdflatex.tex

prezentacio-pdflatex.pdf: prezentacio.tex
	cp prezentacio.tex prezentacio-pdflatex.tex
	pdflatex --shell-escape prezentacio-pdflatex.tex
	pdflatex --shell-escape prezentacio-pdflatex.tex
	rm -f prezentacio-pdflatex.aux
	rm -f prezentacio-pdflatex.log
	rm -f prezentacio-pdflatex.out
	rm -f prezentacio-pdflatex.bbl
	rm -f prezentacio-pdflatex.blg
	rm -f prezentacio-pdflatex.toc
	rm -f prezentacio-pdflatex.tdo
	rm -f prezentacio-pdflatex.tex
	rm -f prezentacio-pdflatex.nav
	rm -f prezentacio-pdflatex.snm

latex.dvi: $(DEPENDSON)
	cp $(NAME).tex latex.tex
	latex latex.tex
	bibtex latex.aux
	latex latex.tex
	latex latex.tex
	rm -f latex.aux
	rm -f latex.log
	rm -f latex.out
	rm -f latex.bbl
	rm -f latex.blg
	rm -f latex.toc
	rm -f latex.tdo
	rm -f latex.tex

prezentacio-latex.dvi: prezentacio.tex
	cp prezentacio.tex prezentacio-latex.tex
	latex prezentacio-latex.tex
	latex prezentacio-latex.tex
	rm -f prezentacio-latex.aux
	rm -f prezentacio-latex.log
	rm -f prezentacio-latex.out
	rm -f prezentacio-latex.bbl
	rm -f prezentacio-latex.blg
	rm -f prezentacio-latex.toc
	rm -f prezentacio-latex.tdo
	rm -f prezentacio-latex.tex
	rm -f prezentacio-latex.nav
	rm -f prezentacio-latex.snm

latex.ps: latex.dvi
	dvips -t a4 -Ppdf -G0 $<

prezentacio-latex.ps: prezentacio-latex.dvi
	dvips -Ppdf -G0 $<

latex.pdf: latex.ps
ifeq ($(windir),)
	ps2pdf -dPDFSETTINGS=/printer -dUseCIEColor=true -sPAPERSIZE=a4 $<
else
	ps2pdf $<
endif

prezentacio-latex.pdf: prezentacio-latex.ps
	ps2pdf $<

.PHONY: clean
clean:
	rm -f pdflatex.aux
	rm -f pdflatex.log
	rm -f pdflatex.out
	rm -f pdflatex.bbl
	rm -f pdflatex.blg
	rm -f pdflatex.toc
	rm -f pdflatex.tdo
	rm -f pdflatex.tex
	rm -f pdflatex.pdf

	rm -f latex.aux
	rm -f latex.log
	rm -f latex.out
	rm -f latex.bbl
	rm -f latex.blg
	rm -f latex.toc
	rm -f latex.tdo
	rm -f latex.tex
	rm -f latex.dvi
	rm -f latex.ps
	rm -f latex.pdf
	
	rm -f prezentacio-pdflatex.aux
	rm -f prezentacio-pdflatex.log
	rm -f prezentacio-pdflatex.out
	rm -f prezentacio-pdflatex.bbl
	rm -f prezentacio-pdflatex.blg
	rm -f prezentacio-pdflatex.toc
	rm -f prezentacio-pdflatex.tdo
	rm -f prezentacio-pdflatex.tex
	rm -f prezentacio-pdflatex.nav
	rm -f prezentacio-pdflatex.snm
	rm -f prezentacio-pdflatex.pdf

	rm -f prezentacio-latex.aux
	rm -f prezentacio-latex.log
	rm -f prezentacio-latex.out
	rm -f prezentacio-latex.bbl
	rm -f prezentacio-latex.blg
	rm -f prezentacio-latex.toc
	rm -f prezentacio-latex.tdo
	rm -f prezentacio-latex.tex
	rm -f prezentacio-latex.nav
	rm -f prezentacio-latex.snm
	rm -f prezentacio-latex.dvi
	rm -f prezentacio-latex.ps
	rm -f prezentacio-latex.pdf

	rm -f $(NAME).pdf
	rm -f prezentacio.pdf
