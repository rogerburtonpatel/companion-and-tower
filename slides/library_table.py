#!/usr/bin/env python3
"""Slide table for the two coinduction libraries.

Reads ../paper-data/library.csv, written by paper-data/measure_library.py.
Writes out/table-library.{png,svg}.
"""
import csv, os

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "paper-data", "library.csv")
OUT = os.path.join(HERE, "out")
INK, MUTED, GRID = "#1a1a19", "#52514E", "#D8D8D4"
GOOD, BAD = "#1BAF7A", "#EB6834"

ROWS = [("Ltac and Tactic Notation", "ltac_lines"),
        ("OCaml plugin", "ocaml_lines"),
        ("OCaml glue in Rocq", "glue_lines"),
        ("plugin build config", "build_lines"),
        (None, None),
        ("total lines", "total_lines"),
        ("total characters", "total_chars")]


def main():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    d = {r["library"]: r for r in csv.DictReader(open(SRC))}
    a, b = d["released"], d["rewritten"]

    body = [r for r in ROWS if r[0]]
    fig, ax = plt.subplots(figsize=(8.0, 0.8 + 0.36 * len(ROWS)), dpi=200)
    fig.patch.set_facecolor("white")
    ax.set_xlim(0, 1); ax.set_ylim(0, len(ROWS) + 1.4); ax.axis("off")
    w = [0.0, 0.60, 0.80, 1.0]

    y = len(ROWS) + 0.7
    for x, h in zip(w, ["", "released", "rewritten", "change"]):
        ax.text(x, y, h, fontsize=10.5, color=MUTED,
                ha="left" if x == 0 else "right", va="center")
    ax.plot([0, 1], [y - 0.42] * 2, color=INK, lw=1.1)

    for i, (label, key) in enumerate(ROWS):
        y = len(ROWS) - i - 0.1
        if label is None:
            ax.plot([0, 1], [y + 0.28] * 2, color=INK, lw=1.0)
            continue
        total = key.startswith("total")
        ax.text(w[0], y, label, fontsize=10.5, color=INK, va="center",
                fontweight="bold" if total else "normal")
        for x, row in ((w[1], a), (w[2], b)):
            ax.text(x, y, f"{int(row[key]):,}", fontsize=10.5, color=INK,
                    ha="right", va="center", fontweight="bold" if total else "normal")
        av, bv = int(a[key]), int(b[key])
        pct = 100 * (bv - av) / av
        ax.text(w[3], y, f"{pct:+.0f}%", fontsize=10.5, ha="right", va="center",
                fontweight="bold", color=GOOD if pct < 0 else BAD)

    ax.plot([0, 1], [0.3] * 2, color=INK, lw=1.1)
    fig.suptitle("The coinduction library's tactic implementation"
                 "   —   every line that exists to implement tactics,"
                 " comments removed",
                 fontsize=11.5, color=INK, y=1.0, x=0.0, ha="left")
    fig.tight_layout(rect=[0, 0, 1, 0.96])
    os.makedirs(OUT, exist_ok=True)
    for ext in ("png", "svg"):
        fig.savefig(os.path.join(OUT, f"table-library.{ext}"),
                    facecolor="white", bbox_inches="tight")
    print(f"  wrote out/table-library.png and .svg")


if __name__ == "__main__":
    main()
