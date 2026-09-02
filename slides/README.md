# Slide data

Reproducible figures for the talk, derived from the same measurements as the
paper. Nothing here modifies a working tree.

## Run it

```
./run.sh                 # build from the existing paper-data/metrics.csv
./run.sh --remeasure     # re-derive metrics.csv from the three checkouts first
```

The first run creates `.venv` and installs the pinned `requirements.txt`. The
`--remeasure` step is the slow one; it materialises each of the three checkouts
into a temp directory and re-counts. Use it when a checkout has moved.

One chart per measure, each with two rows: `theories/` alone, then the whole
development. Every chart is zero-based and labelled with the value and the
change against the paco baseline. Output lands in `out/` as both `.png` (slide
resolution) and `.svg` (vector, for Keynote and Google Slides):

| file | measure |
|---|---|
| `tactic.*` | characters of coinduction-driving Ltac |
| `proof.*`  | characters of proof |
| `def.*`    | characters of definition |
| `total.*`  | total lines of code, every non-blank comment-free line counted once |

Each chart's table also prints to stdout, formatted to paste into a slide.
`./charts.py tactic` builds just one; `--no-chart` prints the tables only.

## What "tactic surface" means

The Ltac that ITrees has to write purely to drive whichever coinduction library
it sits on. It is the client-side cost of adopting the library. It is not the
library's own tactic implementation, which is a separate measure and moves in
the opposite direction. Keep the two apart when presenting them.

Two scopes are reported because they behave differently. `theories/` alone is
the ITrees library proper. `main+extra` adds the four downstream developments
that ship in the same repository. The whole development is the honest headline;
`theories/` alone is where the rewrite did best.

## Reproducibility chain

```
three git checkouts
  -> paper-data/measure.py          curated tactic table, comment-free counting
  -> paper-data/metrics.csv         one row per checkpoint per scope
  -> slides/tactic_surface.py       table, chart, tidy csv
```

`measure.py` fails loudly if its curated tactic table names a definition a
checkout does not have, so it cannot silently rot.
