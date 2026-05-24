.PHONY: run clean

run:
	./runagdatex
	pdflatex -interaction=nonstopmode main
	bibtex main
	pdflatex -interaction=nonstopmode main
	pdflatex -interaction=nonstopmode main

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.ptb main.vtc main.toc
