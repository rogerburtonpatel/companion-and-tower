#!/bin/sh
# Compile probes.v against the rewritten coinduction library.
# Exit status 0 means every claim in probes.v holds.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
COIND=${COIND:-$(cd "$HERE/.." && pwd)}
make -C "$COIND" >/dev/null
OUT=$(mktemp -d); trap 'rm -rf "$OUT"' EXIT
cp "$HERE/probes.v" "$OUT/"
cd "$OUT" && rocq c -Q "$COIND/theories" Coinduction probes.v
echo "all claims in probes.v hold"
