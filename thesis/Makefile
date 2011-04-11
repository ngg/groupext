NAME=szakdoli

.PHONY: all
all: $(NAME).pdf

$(NAME).pdf: $(wildcard *.tex *.eps *.sty *.cls) ref.bib
	pdflatex $(NAME).tex
	bibtex $(NAME).aux
	pdflatex $(NAME).tex
	pdflatex $(NAME).tex
	rm -f $(NAME).aux
	rm -f $(NAME).log
	rm -f $(NAME).out
	rm -f $(NAME).bbl
	rm -f $(NAME).blg
	rm -f $(NAME).toc
	rm -f $(NAME).tdo
	rm -f *-eps-converted-to.pdf

.PHONY: clean
clean:
	rm -f $(NAME).aux
	rm -f $(NAME).log
	rm -f $(NAME).out
	rm -f $(NAME).bbl
	rm -f $(NAME).blg
	rm -f $(NAME).toc
	rm -f $(NAME).tdo
	rm -f $(NAME).pdf
