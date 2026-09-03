# CPP 2027 submission

Definitional Equalities for Substitutions using Rewrite Rules.

    make                  build main.pdf (agdatex, pdflatex, bibtex, pdflatex ×2)
    ./sync-supplement.sh  copy the paper's Agda into supplement/
    ./pagecheck.sh        body length of the submission version

## The paper

| file | |
|---|---|
| `main.tex` | the paper |
| `build/` | scratch for `pagecheck.sh`: the submission version with revision markers stripped, and its page count. Generated, ignored, removed by `make clean` |
| `decisions.tex` | the design-decision figure, not yet `\input` by `main.tex` |
| `references.bib` | bibliography |
| `acmart.cls`, `ACM-Reference-Format.bst` | the ACM class, vendored |
| `agda.sty`, `agdamacros.tex`, `unicodeletters.tex` | the Agda listing style and its unicode table |
| `systemf.tex`, `examples.tex` | one-line wrappers around the generated `latex/` |

Coloured margin markers in the PDF flag what still needs work: `STALE` for text
describing a superseded result, `ADD HERE` for a result that wants a home,
`NOTE` for a decision worth recording.

## The Agda the paper prints

| file | rules | |
|---|---:|---|
| `systemf.agda` | 72 | intrinsically scoped System F and its σ-calculus, maps as functions |
| `systemf-vec.agda` | 72 | the same, maps as inductive vectors; no postulates |
| `closure.agda` | | the rule set's *absences*, eight `refl`s; internal, not shipped |
| `closure-vec.agda` | | the same eight over the vector model; internal |
| `examples.agda` | | the small examples of §2 |
| `systemf.sg` | | the signature of `systemf.agda` in the generator's input format |

`./runagdatex` extracts `systemf.agda` and `examples.agda` into `latex/`; `make`
does it first. It is hash-guarded, so an unchanged file is skipped.

Every module carries its own `{-# OPTIONS --rewriting --local-confluence-check #-}`,
so nothing depends on how `agda` is invoked.

## `supplement/`

The supplementary material, maintained in place. `systemf.agda`, `systemf-vec.agda`
and `examples.agda` are copied from here by `./sync-supplement.sh`; everything
else is authored there. See `supplement/README.md`.

## `memory.md`

Long explanatory prose removed from the Agda module headers when they were
trimmed, kept verbatim with the file and line range it came from. Nothing reads
it; it is there so the reasoning is not lost.

## `trs/`

The rule set exported as a first-order term rewriting system, with AProVE's
termination and confluence proofs and the script that re-checks the subset claim
`trs/TRS.md` makes about them. Reported in §4.3; not part of the supplement.
