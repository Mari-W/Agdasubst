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
        body = i - 1 + (0 if p.strip().startswith('References') else 0)
        # the page where references start is partly body; count it as body
        body = i
        break
print("total pages      :", total)
print("references start :", i if 'References' in "".join(pages) else "n/a")
print("BODY PAGES       :", body, " (limit 12)" , "OK" if body <= 12 else "OVER BY %d" % (body-12))
PY
