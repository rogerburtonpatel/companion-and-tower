# CPP paper source

**This is a typeset outline, not a draft.** The prose is the author's outline
verbatim. Two markers appear throughout and both vanish when `\draftfalse` is
set in `preamble.tex`:

- **`gap`** (blue) marks a blank the outline itself left, such as `<chart>`,
  `<fill in after data collection>`, or a trailing `...`. Where data now exists
  to fill one, the box says what the measurement is.
- **`note`** (amber) is an editorial remark from the typesetting pass: something
  worth adding, a claim the measurements contradict, or a placement decision.
  None of it is paper prose. Delete each as it is resolved.

Section order is derived rather than as-given. Three things in the outline were
out of place: the measurement paragraph above the abstract is methodology and
became Section 3; "Initial Result" stands on its own rather than under the
experiment; and the trailing `monauto` paragraph moved into the rewrite section.
Sections 7 and the data-availability statement are containers that did not exist
in the outline, and their notes say so.

Format is the CPP call for papers requirement: ACM SIGPLAN proceedings format,
`acmart` with the `sigplan` option, 10pt, lightweight double-blind review. The
limit is 12 pages excluding bibliography.

## Building

Locally, with a TeX Live that has `acmart` and `pgfplots`:

```
latexmk -pdf main.tex
```

On Overleaf, upload this directory as a project and compile `main.tex` with
pdfLaTeX. Everything the paper needs is inside this directory, including the
data, so nothing outside it has to be uploaded.

## Where the numbers come from

Nothing in the prose is typed by hand twice. There are two mechanisms.

Tables and the chart read `data/*.csv` at compile time through
`pgfplotstable`. Rerunning the measurement updates them with no editing.

Figures that appear inside sentences are macros defined once in
`preamble.tex`, so a number appears once in the source and every use tracks it.
Build-time figures are generated into `data/timing-macros.tex`.

To refresh everything after re-running `../paper-data/measure.py`:

```
./sync-data.sh
```

That copies the CSVs in, regenerates the display tables and the timing table,
and then runs `check-numbers.py`, which re-derives every figure the prose states
from the data and fails if any of them has drifted. Run `check-numbers.py` on
its own any time.

## The build-time measurement

`data/timings.csv` is four interleaved rounds of a full serial build at each of
the three checkpoints, measured on 2026-08-31. The protocol matters and is
described in Section 3 of the paper. Three confounds each produced a wrong answer
during this work: `make TIMED=1` leaves timing artifacts in one tree and not
another, blocked ordering plus machine warm-up manufactures a difference that is
not there, and a single run cannot resolve a two-second effect on a ninety-second
build. The harness that produced the file is `/private/tmp/cpp-timing`, which
holds a pinned checkout of each checkpoint; it is disposable and rebuildable.

## Layout

```
main.tex              document, \input's everything
preamble.tex          packages, macros, and the prose figures
coqlisting.tex        the listings language for Rocq
sections/             one file per section
figures/              tables and the chart
data/                 CSVs the tables and chart read
gen-tables.py         metrics.csv -> headline.csv, derived.csv, chart.csv
gen-timing.py         timings.csv -> tbl-timing.tex, timing-macros.tex
sync-data.sh          run both, after refreshing the CSVs
```

`data/derived.csv` separates tactic definitions out of the specification column.
Ltac is specification for the measurement script's classifier, so the tactic
surface is counted inside the definition figures; several claims in the paper
turn on separating the two.

## Draft mode

`preamble.tex` sets `\drafttrue`, which enables `todonotes` margin notes. Set
`\draftfalse` for a submission build, and drop `review` from the
`\documentclass` options once the page numbers and line numbers are not wanted.
