# LaTeX Makefile
FILE=dissertacao
CLAUDIA_PATH=~/Dropbox/Work/mestrado/Felipe\ Rodopoulos/dissertacao/

all: build clean

.PHONY: clean

clean:
	@rm -f *.aux *.blg *.out *.bbl *.log *.toc *.lot *.lof *.flo *.fls *.brf *.acn *.glsdefs *.fdb_latexmk *.ist *.glo *.synctex.gz

build:
	@echo "Building..."
	@echo "warn: pdflatex and bibtex output is ommited. For verbosity, use 'make debug'"
	@pdflatex $(FILE) > /dev/null
	@bibtex $(FILE) > /dev/null
	@pdflatex $(FILE) > /dev/null
	@pdflatex $(FILE) > /dev/null
	@echo "Done."

debug:
	@echo "Building..."
	@pdflatex $(FILE)
	@bibtex $(FILE)
	@pdflatex $(FILE) > /dev/null
	@pdflatex $(FILE)
	@echo "Done."


cacau: clean
	@rsync -r * $(CLAUDIA_PATH)
