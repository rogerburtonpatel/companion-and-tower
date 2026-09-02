#!/usr/bin/env python3
"""Tactic surface across the three checkpoints, as a slide table and a chart.

"Tactic surface" means the Ltac that ITrees has to write purely to drive
whichever coinduction library it sits on. It is the client-side cost of adopting
the library, and it is the measure that moved most during this work. It is NOT
the coinduction library's own tactic implementation, which is a separate measure
that moves the other way. Keep the two apart when presenting them.

Reads ../paper-data/metrics.csv. Regenerate that first with:

    cd paper-data && ./measure.py

Usage:
    ./tactic_surface.py                    theories/ (default)
    ./tactic_surface.py --scope main+extra whole development
    ./tactic_surface.py --scope both       both, side by side
    ./tactic_surface.py --no-chart         table only
"""
import csv, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "paper-data", "metrics.csv")
OUT = os.path.join(HERE, "out")

ORDER = ["paco", "old_port", "new_port"]
NICE = {"paco": "paco", "old_port": "old port", "new_port": "new port"}
SCOPE_NICE = {"main": "theories/", "main+extra": "whole development"}
FIELDS = [("library_tactics", "distinct tactics"),
          ("tactic_lines", "lines of Ltac"),
          ("tactic_chars", "characters of Ltac")]


def load():
    if not os.path.exists(SRC):
        sys.exit(f"missing {SRC}\nrun:  cd paper-data && ./measure.py")
    return {(r["checkpoint"], r["scope"]): r
            for r in csv.DictReader(open(SRC))}


def pct(a, b):
    return 100.0 * (b - a) / a


def table(m, scopes):
    """Print the slide table, and return tidy rows for the CSV."""
    tidy = []
    for scope in scopes:
        print(f"\n{SCOPE_NICE[scope]}   ({scope})\n")
        print("  " + "measure".ljust(20)
              + "".join(NICE[c].rjust(11) for c in ORDER)
              + "old vs paco".rjust(15) + "new vs paco".rjust(14))
        print("  " + "-" * 73)
        for field, label in FIELDS:
            vals = [int(m[(c, scope)][field]) for c in ORDER]
            print("  " + label.ljust(20)
                  + "".join(f"{v:,}".rjust(11) for v in vals)
                  + f"{pct(vals[0], vals[1]):+.1f}%".rjust(15)
                  + f"{pct(vals[0], vals[2]):+.1f}%".rjust(14))
            for c, v in zip(ORDER, vals):
                tidy.append({"scope": scope, "checkpoint": c, "measure": field,
                             "value": v, "pct_vs_paco": round(pct(vals[0], v), 2)})
    return tidy


def headline(m, scope):
    a, b, c = (int(m[(k, scope)]["tactic_chars"]) for k in ORDER)
    print("\n" + "=" * 73)
    print(f"HEADLINE   characters of coinduction-driving Ltac, {SCOPE_NICE[scope]}")
    print(f"  paco {a:,}   ->   old port {b:,}   ->   new port {c:,}")
    print(f"  the first port  {pct(a, b):+.0f}%")
    print(f"  after rewrite   {pct(a, c):+.1f}%")
    print("=" * 73)


def chart(m, scope):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    # Palette validated for colourblind separation; same one the paper uses.
    COL = {"paco": "#2A78D6", "old_port": "#EB6834", "new_port": "#1BAF7A"}
    INK, MUTED, GRID = "#1a1a19", "#52514E", "#D8D8D4"

    fig, axes = plt.subplots(1, 3, figsize=(12, 4.2), dpi=200)
    fig.patch.set_facecolor("white")

    for ax, (field, label) in zip(axes, FIELDS):
        vals = [int(m[(c, scope)][field]) for c in ORDER]
        bars = ax.bar(range(3), vals, width=0.6,
                      color=[COL[c] for c in ORDER], zorder=3)
        base, top = vals[0], max(vals)
        for i, (bar, v) in enumerate(zip(bars, vals)):
            x = bar.get_x() + bar.get_width() / 2
            ax.text(x, v + top * 0.035, f"{v:,}", ha="center", va="bottom",
                    fontsize=11, color=INK, fontweight="bold")
            if i:
                ax.text(x, v + top * 0.125, f"{pct(base, v):+.0f}%",
                        ha="center", va="bottom", fontsize=10.5, color=MUTED)
        ax.set_xticks(range(3), [NICE[c] for c in ORDER], fontsize=10.5, color=INK)
        ax.set_ylim(0, top * 1.32)
        ax.set_title(label, fontsize=12, color=INK, pad=10)
        ax.yaxis.grid(True, color=GRID, lw=0.8, zorder=0)
        ax.set_axisbelow(True)
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        for s in ("left", "bottom"):
            ax.spines[s].set_color(GRID)
        ax.tick_params(colors=MUTED, length=0, labelsize=9.5)
        ax.yaxis.set_major_formatter(plt.FuncFormatter(lambda v, _: f"{int(v):,}"))

    fig.suptitle(f"Tactic surface in {SCOPE_NICE[scope]}: "
                 "Ltac written only to scaffold the coinduction library",
                 fontsize=13, color=INK, y=0.99)
    fig.tight_layout(rect=[0, 0, 1, 0.93])
    os.makedirs(OUT, exist_ok=True)
    tag = "theories" if scope == "main" else "whole"
    for ext in ("png", "svg"):
        p = os.path.join(OUT, f"tactic-surface-{tag}.{ext}")
        fig.savefig(p, facecolor="white", bbox_inches="tight")
    print(f"\nwrote {OUT}/tactic-surface-{tag}.png and .svg")


def main():
    argv = sys.argv[1:]
    scope = "main"
    if "--scope" in argv:
        scope = argv[argv.index("--scope") + 1]
    scopes = ["main", "main+extra"] if scope == "both" else [scope]
    for s in scopes:
        if s not in SCOPE_NICE:
            sys.exit(f"unknown scope {s!r}; use main, main+extra, or both")

    m = load()
    tidy = table(m, scopes)
    for s in scopes:
        headline(m, s)

    os.makedirs(OUT, exist_ok=True)
    path = os.path.join(OUT, "tactic-surface.csv")
    with open(path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["scope", "checkpoint", "measure",
                                          "value", "pct_vs_paco"])
        w.writeheader()
        w.writerows(tidy)
    print(f"\nwrote {path}")

    if "--no-chart" not in argv:
        for s in scopes:
            chart(m, s)


if __name__ == "__main__":
    main()
