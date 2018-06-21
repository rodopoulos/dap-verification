# LaTeX Makefile
FILE=dissertacao
CLAUDIA_PATH=~/Dropbox/Work/mestrado/Felipe\ Rodopoulos/dissertacao/

all: build clean

.PHONY: clean

clean:
	@rm -f *.aux *.blg *.out *.bbl *.log *.toc *.lot *.lof *.flo *.fls *.brf *.acn *.glsdefs *.fdb_latexmk *.ist *.glo *.synctex.gz

build:
	@echo "Compilando Latex com PDFLatex e BibTeX..."
	@pdflatex $(FILE) > /dev/null
	@pdflatex $(FILE) > /dev/null
	@bibtex $(FILE) > /dev/null
	@pdflatex $(FILE) > /dev/null
	@pdflatex $(FILE) > /dev/null
	@echo "Feito."

cacau: clean
	cp -r * $(CLAUDIA_PATH)
