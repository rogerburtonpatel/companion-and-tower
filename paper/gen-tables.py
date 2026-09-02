#!/usr/bin/env python3
"""Derive the paper's display tables from paper-data/metrics.csv.

Produces data/headline.csv (display labels, so LaTeX never sees an underscore)
and data/chart.csv (wide format for the small multiples), plus data/derived.csv
which separates tactic code out of the definition column."""
import csv

LABEL = {"paco": "paco", "old_port": "old port", "new_port": "new port"}
SCOPE = {"main": "main", "main+extra": "main+extra"}

rows = list(csv.DictReader(open("data/metrics.csv")))

with open("data/headline.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["checkpoint", "scope", "tactics", "tlines", "tchars",
                "dlines", "dchars", "plines", "pchars"])
    for r in rows:
        w.writerow([LABEL[r["checkpoint"]], SCOPE[r["scope"]],
                    r["library_tactics"], r["tactic_lines"], r["tactic_chars"],
                    r["def_lines"], r["def_chars"],
                    r["proof_lines"], r["proof_chars"]])

with open("data/derived.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["checkpoint", "scope", "tactic_lines", "nontactic_def_lines",
                "proof_lines", "tactic_chars", "nontactic_def_chars", "proof_chars"])
    for r in rows:
        w.writerow([r["checkpoint"], r["scope"], r["tactic_lines"],
                    int(r["def_lines"]) - int(r["tactic_lines"]), r["proof_lines"],
                    r["tactic_chars"],
                    int(r["def_chars"]) - int(r["tactic_chars"]), r["proof_chars"]])

idx = {(r["checkpoint"], r["scope"]): r for r in rows}
with open("data/chart.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["idx", "label", "tactic_lines", "nontactic_def_lines", "proof_lines"])
    for i, cp in enumerate(["paco", "old_port", "new_port"]):
        r = idx[(cp, "main+extra")]
        w.writerow([i, LABEL[cp], r["tactic_lines"],
                    int(r["def_lines"]) - int(r["tactic_lines"]), r["proof_lines"]])
print(open("data/headline.csv").read())
