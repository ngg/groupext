NAME=szakdoli

.PHONY: all
all: dvi ps pdf

.PHONY: dvi ps pdf
dvi: $(NAME).dvi
ps: $(NAME).ps
pdf: $(NAME).pdf


$(NAME).dvi: $(wildcard *.tex */*.tex */*/*.tex */*/*/*.tex *.eps */*.eps */*/*.eps */*/*/*.eps)
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
	rm -f $(NAME).tdo

$(NAME).ps: $(NAME).dvi
	dvips -t a4 -Ppdf -G0 $(NAME).dvi

$(NAME).pdf: $(NAME).ps
	ps2pdf -dPDFSETTINGS=/printer -dUseCIEColor=true $(NAME).ps

.PHONY: clean
clean:
	rm -f $(NAME).aux
	rm -f $(NAME).log
	rm -f $(NAME).out
	rm -f $(NAME).bbl
	rm -f $(NAME).blg
	rm -f $(NAME).toc
	rm -f $(NAME).tdo
	rm -f $(NAME).dvi
	rm -f $(NAME).ps
	rm -f $(NAME).pdf
