#!/usr/bin/env bash
# Body length of the SUBMISSION version: revision markers stripped, references
# not counted.  CPP allows 12 pages excluding the bibliography.
set -eu
cd "$(dirname "$0")"
python3 - <<'PY'
t = open('main.tex').read()
t = t.replace("\\newcommand{\\RWnote}[1]{{\\color{rewC}\\sffamily\\bfseries\\small$\\blacktriangleright$\\,REWRITTEN: #1}}",
              "\\newcommand{\\RWnote}[1]{}")
t = t.replace("\\newcommand{\\RW}[1]{{\\color{rewC}#1}}", "\\newcommand{\\RW}[1]{#1}")
t = t.replace("""\\newcommand{\\MarkBlock}[2]{%
  \\par\\smallskip\\noindent\\textcolor{#1}{\\rule{\\linewidth}{0.9pt}}%
  \\par\\nopagebreak\\noindent{\\color{#1}\\sffamily\\footnotesize #2}%
  \\par\\nopagebreak\\noindent\\textcolor{#1}{\\rule{\\linewidth}{0.9pt}}\\par\\smallskip}""",
              "\\newcommand{\\MarkBlock}[2]{}")
open('main-sub.tex','w').write(t)
PY
cp -f main.bbl main-sub.bbl 2>/dev/null || true
pdflatex -interaction=nonstopmode -halt-on-error main-sub >/dev/null 2>&1
pdflatex -interaction=nonstopmode -halt-on-error main-sub >/dev/null 2>&1
pdftotext main-sub.pdf main-sub.txt 2>/dev/null
python3 - <<'PY'
pages = open('main-sub.txt').read().split(chr(12))
total = len([p for p in pages if p.strip()])
body = total
for i, p in enumerate(pages, 1):
    if 'References' in p:
        # The references page counts as a body page only if body text
        # precedes the heading on it.  Drop the line-number column and the
        # running head, then look at what comes before "References".
        import re as _re
        lines = [l for l in p.split("\n")
                 if l.strip() and not _re.fullmatch(r"\d{3,4}", l.strip())
                 and 'CPP ' not in l and 'Rewrite Rules' not in l]
        before = lines[:lines.index('References')] if 'References' in lines else lines
        body = i if before else i - 1
        break
print("total pages      :", total)
print("references start :", i if 'References' in "".join(pages) else "n/a")
print("BODY PAGES       :", body, " (limit 12)" , "OK" if body <= 12 else "OVER BY %d" % (body-12))
PY
