#!/usr/bin/env python3
"""Slide charts for the three checkpoints.

One chart per measure, each with two rows: theories/ alone, then the whole
development. Bars are zero-based and labelled with the value and the change
against the paco baseline.

Reads ../paper-data/metrics.csv. Regenerate that first with:

    cd paper-data && ./measure.py

Usage:
    ./charts.py              all four measures
    ./charts.py tactic       just one, by key below
"""
import csv, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "paper-data", "metrics.csv")
OUT = os.path.join(HERE, "out")

ORDER = ["paco", "old_port", "new_port"]
NICE = {"paco": "paco", "old_port": "old port", "new_port": "new port"}
SCOPES = [("main", "theories/ alone"), ("main+extra", "whole development")]
SHORT = {"main": "theories/", "main+extra": "whole dev"}

# key -> (csv column, chart title, axis label)
MEASURES = {
    "tactic": ("tactic_chars", "Tactic surface", "chars of Ltac"),
    "proof":  ("proof_chars",  "Proof size",     "characters"),
    "def":    ("def_chars",    "Definition size", "characters"),
    "total":  ("code_lines",   "Total size",     "lines of code"),
}

COL = {"paco": "#2A78D6", "old_port": "#EB6834", "new_port": "#1BAF7A"}
INK, MUTED, GRID = "#1a1a19", "#52514E", "#D8D8D4"


def load():
    if not os.path.exists(SRC):
        sys.exit(f"missing {SRC}\nrun:  cd paper-data && ./measure.py")
    return {(r["checkpoint"], r["scope"]): r for r in csv.DictReader(open(SRC))}


def pct(a, b):
    return 100.0 * (b - a) / a


def table(m, key):
    col, title, _ = MEASURES[key]
    print(f"\n{title}  ({col})\n")
    print("  " + "scope".ljust(20) + "".join(NICE[c].rjust(11) for c in ORDER)
          + "old vs paco".rjust(15) + "new vs paco".rjust(14))
    print("  " + "-" * 73)
    for scope, label in SCOPES:
        v = [int(m[(c, scope)][col]) for c in ORDER]
        print("  " + label.ljust(20) + "".join(f"{x:,}".rjust(11) for x in v)
              + f"{pct(v[0], v[1]):+.1f}%".rjust(15)
              + f"{pct(v[0], v[2]):+.1f}%".rjust(14))


def chart(m, key):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    col, title, ylabel = MEASURES[key]
    fig, axes = plt.subplots(2, 1, figsize=(7.2, 7.0), dpi=200)
    fig.patch.set_facecolor("white")

    for ax, (scope, label) in zip(axes, SCOPES):
        vals = [int(m[(c, scope)][col]) for c in ORDER]
        bars = ax.bar(range(3), vals, width=0.55,
                      color=[COL[c] for c in ORDER], zorder=3)
        base, top = vals[0], max(vals)
        for i, (bar, v) in enumerate(zip(bars, vals)):
            x = bar.get_x() + bar.get_width() / 2
            ax.text(x, v + top * 0.035, f"{v:,}", ha="center", va="bottom",
                    fontsize=11.5, color=INK, fontweight="bold")
            if i:
                ax.text(x, v + top * 0.125, f"{pct(base, v):+.1f}%",
                        ha="center", va="bottom", fontsize=10.5, color=MUTED)
        ax.set_xticks(range(3), [NICE[c] for c in ORDER], fontsize=11, color=INK)
        ax.set_ylim(0, top * 1.32)
        ax.set_title(label, fontsize=12, color=INK, pad=8)
        ax.set_ylabel(ylabel, fontsize=10, color=MUTED)
        ax.yaxis.grid(True, color=GRID, lw=0.8, zorder=0)
        ax.set_axisbelow(True)
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        for s in ("left", "bottom"):
            ax.spines[s].set_color(GRID)
        ax.tick_params(colors=MUTED, length=0, labelsize=9.5)
        ax.yaxis.set_major_formatter(plt.FuncFormatter(lambda v, _: f"{int(v):,}"))

    fig.suptitle(title, fontsize=14, color=INK, y=0.985)
    fig.tight_layout(rect=[0, 0, 1, 0.95])
    os.makedirs(OUT, exist_ok=True)
    for ext in ("png", "svg"):
        fig.savefig(os.path.join(OUT, f"{key}.{ext}"),
                    facecolor="white", bbox_inches="tight")
    plt.close(fig)
    print(f"  wrote out/{key}.png and .svg")


def table_png(m, keys, name, title):
    """Render the tables as an image, for pasting into a slide."""
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    rows = []
    for k in keys:
        col, mtitle, _ = MEASURES[k]
        for i, (scope, label) in enumerate(SCOPES):
            v = [int(m[(c, scope)][col]) for c in ORDER]
            rows.append((mtitle if i == 0 else "", SHORT[scope],
                         [f"{x:,}" for x in v],
                         pct(v[0], v[1]), pct(v[0], v[2])))

    # With one measure the title already names it, so the measure column goes.
    single = len(keys) == 1
    w = ([-1, 0.0, 0.42, 0.565, 0.71, 0.86, 1.0] if single
         else [0.0, 0.175, 0.45, 0.59, 0.735, 0.875, 1.0])
    fh = 0.8 + 0.36 * len(rows) + 0.16 * (len(keys) - 1)
    fig, ax = plt.subplots(figsize=(8.4 if single else 9.6, fh), dpi=200)
    fig.patch.set_facecolor("white")
    ax.set_xlim(0, 1); ax.set_ylim(0, len(rows) + 1.6); ax.axis("off")

    head = ["", "", "paco", "old port", "new port", "old vs paco", "new vs paco"]
    y = len(rows) + 0.85
    for i in range(7):
        if single and i == 0:
            continue
        ax.text(w[i], y, head[i], fontsize=10.5, color=MUTED,
                ha="left" if i < 2 else "right", va="center")
    ax.plot([0, 1], [y - 0.42] * 2, color=INK, lw=1.1)

    for r, (mt, label, vals, d1, d2) in enumerate(rows):
        y = len(rows) - r - 0.1
        if mt and not single:
            ax.text(w[0], y, mt, fontsize=10.5, color=INK,
                    fontweight="bold", va="center")
        ax.text(w[1], y, label, fontsize=10, color=MUTED, va="center")
        for i, v in enumerate(vals):
            ax.text(w[2 + i], y, v, fontsize=10.5, color=INK,
                    ha="right", va="center")
        for i, d in enumerate((d1, d2)):
            ax.text(w[5 + i], y, f"{d:+.1f}%", fontsize=10.5, ha="right",
                    va="center", fontweight="bold",
                    color="#1BAF7A" if d < 0 else "#EB6834")
        if r and not mt:
            continue
        if r:
            ax.plot([0, 1], [y + 0.5] * 2, color=GRID, lw=0.7)

    ax.plot([0, 1], [0.32] * 2, color=INK, lw=1.1)
    fig.suptitle(title, fontsize=13, color=INK, y=1.0, x=0.0, ha="left")
    fig.tight_layout(rect=[0, 0, 1, 0.97])
    os.makedirs(OUT, exist_ok=True)
    for ext in ("png", "svg"):
        fig.savefig(os.path.join(OUT, f"{name}.{ext}"),
                    facecolor="white", bbox_inches="tight")
    plt.close(fig)
    print(f"  wrote out/{name}.png and .svg")


def main():
    keys = [a for a in sys.argv[1:] if not a.startswith("-")] or list(MEASURES)
    for k in keys:
        if k not in MEASURES:
            sys.exit(f"unknown measure {k!r}; pick from {', '.join(MEASURES)}")
    m = load()
    for k in keys:
        table(m, k)
        if "--no-chart" not in sys.argv:
            chart(m, k)
    if "--no-chart" not in sys.argv:
        for k in keys:
            table_png(m, [k], f"table-{k}",
                      f"{MEASURES[k][1]} ({MEASURES[k][2]})")
        if len(keys) > 1:
            table_png(m, keys, "table-all",
                      "ITrees metrics across the three checkpoints"
                      " (sizes in characters, total size in lines)")


if __name__ == "__main__":
    main()
