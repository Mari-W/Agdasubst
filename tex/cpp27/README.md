# CPP 2027 submission

    make                 build main.pdf  (agdatex, pdflatex, bibtex, pdflatex ×2)
    ./mksupplement.sh    assemble supplement/ from here and ../cpp27
    ./mksupplement.sh --zip   …and zip it

## Top level — the paper

| file | |
|---|---|
| `main.tex` | the paper |
| `decisions.tex` | the design-decision figure; not yet `\input` — see the `\AddHere` marker in §5 |
| `references.bib`, `main.bbl` | bibliography |
| `acmart.cls`, `ACM-Reference-Format.bst` | the ACM class, vendored |
| `agda.sty`, `agdamacros.tex`, `unicodeletters.tex` | the Agda listing style and its unicode table |
| `systemf.tex`, `examples.tex` | one-line wrappers around `latex/` |
| `latex/` | agdatex output — generated, do not edit |

Coloured margin markers in the PDF flag what still needs work:
`STALE` (text describing a superseded result), `ADD HERE` (a new result that
wants a home), `NOTE` (a decision worth recording).

## Top level — the Agda the paper prints

| file | |
|---|---|
| `systemf.agda` | intrinsically scoped System F and its σ-calculus, 72 rewrite rules |
| `examples.agda` | the small examples of §2 |
| `closure.agda` | the rule set's *absences*, checked: eight `refl`s, one per place a completion operator needs no image |
| `systemf.sig` | the same signature in the generator's input format |

`./runagdatex` re-extracts both into `latex/`; `make` does it for you.  It is
hash-guarded, so an unchanged file is skipped.

## `supplement/`

Assembled by `./mksupplement.sh`, never edited by hand.  Its single README is
authored in `doc/supplement-README.md`, so it is versioned with the source
rather than regenerated.

It holds the Agda (`systemf.agda`, `examples.agda`, `closure.agda`, the POPLmark
development), the generator that emits `poplmark/Core/`, and the exported TRS
with AProVE's termination and confluence proofs.  Nothing else: no build
scripts, no `.ari` exports, no tool-survey pages, no superseded probes.
