NAME=szakdoli

.PHONY: all
all: $(NAME).pdf

$(NAME).pdf: pdflatex.pdf
	cp $< $@

.PHONY: both
both: latex.pdf pdflatex.pdf


pdflatex.pdf: $(wildcard *.tex *.eps *.sty *.cls *.bib)
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

latex.dvi: $(wildcard *.tex *.eps *.sty *.cls *.bib)
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

latex.ps: latex.dvi
	dvips -t a4 -Ppdf -G0 $<

latex.pdf: latex.ps
ifeq ($(windir),)
	ps2pdf -dPDFSETTINGS=/printer -dUseCIEColor=true -sPAPERSIZE=a4 $<
else
	ps2pdf $<
endif

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

	rm -f $(NAME).pdf
