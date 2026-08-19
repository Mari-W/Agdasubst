#!/usr/bin/env bash
# DISABLED 2026-08-19.  supplement/ is now edited IN PLACE and is the working
# tree, not generated output.  This script does `rm -rf supplement` and re-copies
# from ../cpp27, which destroyed hand edits made in supplement/ (agdasubst.py's
# type fixes and the trimmed AProVE proof texts).  Do not run it without first
# porting supplement/ back into the source tree.
echo "mksupplement.sh is disabled: supplement/ is hand-maintained now." >&2
echo "Remove this guard only after reconciling supplement/ with ../cpp27." >&2
exit 1

# Assemble supplement/ — the Agda, and the two external proofs.
#
#   ./mksupplement.sh          build supplement/
#   ./mksupplement.sh --zip    and zip it
#
# Nothing is authored in supplement/ except doc/supplement-README.md, which is
# copied in as its README.  Re-run after any change.
set -eu
cd "$(dirname "$0")"
SRC=../cpp27
DEST=supplement
rm -rf "$DEST"
mkdir -p "$DEST/poplmark" "$DEST/generator" "$DEST/trs"

# the development the paper is about
cp systemf.agda examples.agda closure.agda "$DEST/"

# POPLmark: the metatheory and the cores it sits on
cp -r "$SRC"/poplmark/{Sigma,Challenge,Reloaded} "$DEST/poplmark/"
cp "$SRC"/poplmark/check.sh "$DEST/poplmark/"
# The Part-3 test harness carries no substitution reasoning at all -- 571
# lines, zero uses of a traversal -- and needs ~76 min to check.  Animation
# itself, which IS Part 3's deliverable, stays.
rm -f "$DEST"/poplmark/Challenge/{Test1,Test2,Test3,Test4,Test5,Test6,Test7,Suite,Timing}.agda
# ...so check.sh's Suite special case has nothing left to skip
python3 - "$DEST/poplmark/check.sh" <<'PY'
import sys, re
p = sys.argv[1]; s = open(p).read()
s = s.replace("""#   ./check.sh          every module except Challenge/Suite.agda
#   ./check.sh --all    including it (~76 min in one module; the seven
#                       Challenge/Test*.agda modules cover it)
""", """#   ./check.sh          typecheck every module
""")
s = re.sub(r"  case \"\$f\" in\n    Challenge/Suite\.agda\).*?\n  esac\n", "", s, flags=re.S)
open(p, "w").write(s)
PY

# the generator that emits Sigma/, and its inputs
cp "$SRC"/poplmark/gen/agdasubst.py "$DEST/generator/"
cp -r "$SRC"/poplmark/gen/signatures "$DEST/generator/"

# the rule set as a TRS, and the proofs about it
cp "$SRC"/coco/systemf.trs "$SRC"/TRS.md "$DEST/trs/"
cp "$SRC"/coco/out/sigma-fcr.SN.PROOF.txt   "$DEST/trs/termination-aprove.txt"
cp "$SRC"/coco/out/sigma-fcr.CR.solvers.txt "$DEST/trs/confluence-aprove.txt"
# the script that re-checks the subset claim TRS.md makes about those proofs
cp "$SRC"/coco/check_archives.py "$DEST/trs/"

cp doc/supplement-README.md "$DEST/README.md"

find "$DEST" \( -name '*.agdai' -o -name '*.pyc' -o -name '.DS_Store' \) -delete
find "$DEST" -name '__pycache__' -type d -prune -exec rm -rf {} +
chmod +x "$DEST/poplmark/check.sh"

printf '\n── supplement/ ──\n'
find "$DEST" -type f | sort | sed "s|^$DEST/|  |"
printf '\n%s files, %s lines of Agda, %s\n' \
  "$(find "$DEST" -type f | wc -l)" \
  "$(find "$DEST" -name '*.agda' -exec cat {} + | wc -l)" \
  "$(du -sh "$DEST" | cut -f1)"

if [ "${1:-}" = "--zip" ]; then
  rm -f supplement.zip; zip -qr supplement.zip "$DEST"; ls -la supplement.zip
fi
