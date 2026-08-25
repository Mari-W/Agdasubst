#!/usr/bin/env bash
# Copy the paper's Agda into supplement/.  closure.agda and closure-vec.agda
# are internal checks and are deliberately not shipped.
set -eu
cd "$(dirname "$0")"
cp systemf.agda systemf-vec.agda examples.agda supplement/
find supplement -name '*.agdai' -delete
echo "supplement/ synced"
