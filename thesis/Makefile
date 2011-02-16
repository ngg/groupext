NAME=szakdoli

.PHONY: all
all: dvi ps pdf

.PHONY: dvi ps pdf
dvi: $(NAME).dvi
ps: $(NAME).ps
pdf: $(NAME).pdf


$(NAME).dvi: $(wildcard *.tex */*.tex */*/*.tex */*/*/*.tex)
	latex $(NAME).tex
	bibtex $(NAME).aux
	latex $(NAME).tex
	latex $(NAME).tex
	rm -f $(NAME).aux
	rm -f $(NAME).log
	rm -f $(NAME).out
	rm -f $(NAME).bbl
	rm -f $(NAME).blg
	rm -f $(NAME).toc

$(NAME).ps: $(NAME).dvi
	dvips -Ppdf -G0 $(NAME).dvi

$(NAME).pdf: $(NAME).ps
	ps2pdf $(NAME).ps

.PHONY: clean
clean:
	rm -f $(NAME).aux
	rm -f $(NAME).log
	rm -f $(NAME).out
	rm -f $(NAME).bbl
	rm -f $(NAME).blg
	rm -f $(NAME).toc
	rm -f $(NAME).dvi
	rm -f $(NAME).ps
	rm -f $(NAME).pdf
