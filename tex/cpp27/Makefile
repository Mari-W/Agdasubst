.PHONY: run check clean

# latexmk decides how many pdflatex passes are needed and whether to run bibtex,
# and skips the build entirely when nothing has changed. -pdflatex= carries the
# engine flags: pdflatex alone stops at the `?` prompt on any LaTeX error and
# then dies on EOF, so the build must be non-interactive. -halt-on-error makes a
# real error fail the target instead of being buried in the log.
LATEXMK = latexmk -pdf -synctex=1 \
	  -pdflatex="pdflatex -synctex=1 -interaction=nonstopmode -halt-on-error %O %S"

run:
	./runagdatex
	$(LATEXMK) main
	@echo "── $$(pdfinfo main.pdf | awk '/^Pages/{print $$2}') pages (with revision markers) ──"

# Submission length: strips revision markers and re-typesets from scratch, so it
# costs two extra pdflatex passes (~4.5s) on top of the build. Deliberately NOT
# part of `run`, so the edit-rebuild loop stays fast. Run it when the page budget
# actually matters.
check:
	@./pagecheck.sh

clean:
	latexmk -c main || true
	rm -f main.aux main.log main.out main.blg main.ptb main.vtc main.synctex.gz main.bbl
	rm -f main.fdb_latexmk main.fls
	rm -rf build latex .agdatex-hashes-*.json
	find . -name '*.agdai' -not -path './bak/*' -delete
