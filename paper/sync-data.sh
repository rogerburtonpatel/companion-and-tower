#!/bin/bash
# Refresh the paper's copies of the measurement data from ../paper-data, then
# regenerate the display tables the LaTeX reads.
#
# The paper reads data/*.csv rather than ../paper-data/*.csv so that the paper
# directory is self-contained and can be uploaded to Overleaf on its own.
# Run this after re-running paper-data/measure.py.
set -eu
cd "$(dirname "$0")"
SRC=../paper-data
changed=0
for f in metrics.csv metrics-tactics.csv; do
  if ! cmp -s "$SRC/$f" "data/$f"; then
    echo "updating data/$f"; cp "$SRC/$f" "data/$f"; changed=1
  fi
done
python3 gen-tables.py > /dev/null
echo "regenerated data/headline.csv data/derived.csv data/chart.csv"
if [ -f /private/tmp/cpp-timing/timings.csv ]; then
  python3 gen-timing.py > /dev/null
  echo "regenerated figures/tbl-timing.tex data/timing-macros.tex"
else
  echo "note: no timings.csv found; timing table left as is"
fi
[ "$changed" -eq 0 ] && echo "csv copies were already current"

echo
python3 check-numbers.py
