.PHONY: run clean

# `pdflatex main` alone stops at the `?` prompt on any LaTeX error and then
# dies on EOF, so the build must be non-interactive.  -halt-on-error makes a
# real error fail the target instead of being buried in the log.
LATEX = pdflatex -interaction=nonstopmode -halt-on-error

run:
	./runagdatex
	$(LATEX) main
	bibtex main || true
	$(LATEX) main
	$(LATEX) main
	@echo "── $$(pdfinfo main.pdf | awk '/^Pages/{print $$2}') pages (with revision markers) ──"
	@./pagecheck.sh

clean:
	rm -f main.aux main.log main.out main.blg main.ptb main.vtc main.bbl
	rm -rf build latex .agdatex-hashes-*.json
	find . -name '*.agdai' -not -path './bak/*' -delete
