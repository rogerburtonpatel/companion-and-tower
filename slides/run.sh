#!/bin/bash
# Build the slide data and figures from scratch.
#
# Step 1 (slow, optional) re-derives the measurements from the three checkouts.
# Skip it if paper-data/metrics.csv is already current; nothing here modifies a
# working tree.
#
#   ./run.sh --remeasure    re-run measure.py first, then build
#   ./run.sh                build from the existing metrics.csv
set -eu
cd "$(dirname "$0")"

if [ ! -d .venv ]; then
  echo "== creating venv =="
  python3 -m venv .venv
  ./.venv/bin/pip install --quiet --upgrade pip
  ./.venv/bin/pip install --quiet -r requirements.txt
fi

if [ "${1:-}" = "--remeasure" ]; then
  echo "== re-deriving paper-data/metrics.csv from the three checkouts =="
  ( cd ../paper-data && ./measure.py )
fi

./.venv/bin/python charts.py "$@"
