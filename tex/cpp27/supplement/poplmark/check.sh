#!/bin/sh
# Typecheck every module of the development and tabulate the result.
#
#   ./check.sh          the development, about 15 minutes
#
# Error classes are counted as occurrences of `error: [`, never as one
# hard-coded string: --local-confluence-check and --confluence-check report
# DIFFERENT classes (RewriteNonConfluent vs RewriteAmbiguousRules).
cd "$(dirname "$0")" || exit 1
find Languages Challenge Reloaded -name '*.agdai' -delete 2>/dev/null

modules="Languages/STLC.agda Languages/STLCSums.agda Languages/Fsub.agda
         Languages/FsubRecords.agda Languages/FsubPatterns.agda
         Challenge/Subtyping.agda Challenge/Records.agda Challenge/Patterns.agda
         Reloaded/Soundness.agda Reloaded/Normalization.agda
         Reloaded/SumsSoundness.agda Reloaded/SumsNormalization.agda
         Reloaded/SumsCommuting.agda"
printf '%-30s %6s %5s %8s %6s %7s\n' module lines exit classes pairs wall
fail=0
for f in $modules; do
  log=$(mktemp)
  t0=$(date +%s)
  agda "$f" > "$log" 2>&1
  e=$?
  t=$(( $(date +%s) - t0 ))
  printf '%-30s %6s %5s %8s %6s %6ss\n' "${f%.agda}" "$(wc -l < "$f")" "$e" \
    "$(grep -c 'error: \[' "$log")" \
    "$(grep -c 'RewriteNonConfluent' "$log")" "$t"
  [ "$e" -eq 0 ] || { fail=1; sed -n '1,40p' "$log"; }
  rm -f "$log"
done
exit $fail
