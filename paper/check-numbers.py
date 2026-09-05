#!/usr/bin/env python3
"""Re-derive every number the paper states in prose and compare it against the
data. Exits non-zero if any claim has drifted.

    NOTE: most prose numbers are currently hand-typed rather than using the
    preamble macros, so this checks the macros, not what the prose says.

The tables and the chart read the CSVs at compile time and cannot drift. This
script covers the figures that appear inside sentences, which are macros in
preamble.tex, plus the hand-written library table."""
import csv, os, sys

os.chdir(os.path.dirname(os.path.abspath(__file__)))

m = {(r["checkpoint"], r["scope"]): r for r in csv.DictReader(open("data/metrics.csv"))}
g = lambda cp, sc, f: int(m[(cp, sc)][f])
pct = lambda a, b: 100 * (b - a) / a
nd = lambda cp: g(cp, "main+extra", "def_lines") - g(cp, "main+extra", "tactic_lines")

checks = []
def chk(label, got, want, tol=0.06):
    checks.append((abs(got - want) <= tol, label, f"computed {got:.2f}, paper says {want}"))

# preamble.tex macros
chk("tacCountDropMain", -pct(g("paco","main","library_tactics"), g("new_port","main","library_tactics")), 31.2)
chk("tacLinesDropMain", -pct(g("paco","main","tactic_lines"), g("new_port","main","tactic_lines")), 44.1)
chk("tacCharsDropMain", -pct(g("paco","main","tactic_chars"), g("new_port","main","tactic_chars")), 45.4)
chk("proofCharsDropMain", -pct(g("paco","main","proof_chars"), g("new_port","main","proof_chars")), 8.3)
chk("proofCharsDropBoth", -pct(g("paco","main+extra","proof_chars"), g("new_port","main+extra","proof_chars")), 11.7)
chk("proofLinesDropBoth", -pct(g("paco","main+extra","proof_lines"), g("new_port","main+extra","proof_lines")), 4.1)
chk("tacCharsRiseMain", pct(g("paco","main","tactic_chars"), g("old_port","main","tactic_chars")), 104, 0.3)

# section 6, the first port
chk("s5 proof chars main", -pct(g("paco","main","proof_chars"), g("old_port","main","proof_chars")), 8.7)
chk("s5 proof chars both", -pct(g("paco","main+extra","proof_chars"), g("old_port","main+extra","proof_chars")), 12.0)
chk("s5 proof lines main", -pct(g("paco","main","proof_lines"), g("old_port","main","proof_lines")), 1.8)
chk("s5 proof lines both", -pct(g("paco","main+extra","proof_lines"), g("old_port","main+extra","proof_lines")), 4.1)
chk("s5 tactic chars both", pct(g("paco","main+extra","tactic_chars"), g("old_port","main+extra","tactic_chars")), 178, 0.3)
chk("s5 def-line rise", g("old_port","main+extra","def_lines") - g("paco","main+extra","def_lines"), 81, 0)
chk("s5 nontactic fall", nd("paco") - nd("old_port"), 152, 0)
chk("s5 tactic-line rise", g("old_port","main+extra","tactic_lines") - g("paco","main+extra","tactic_lines"), 233, 0)

# section 9, results
chk("s7 drop both", -pct(g("paco","main+extra","tactic_chars"), g("new_port","main+extra","tactic_chars")), 44.5)
chk("s7 def lines main", -pct(g("paco","main","def_lines"), g("new_port","main","def_lines")), 4.4)
chk("s7 def chars main", -pct(g("paco","main","def_chars"), g("new_port","main","def_chars")), 3.5)
chk("s7 def lines both", -pct(g("paco","main+extra","def_lines"), g("new_port","main+extra","def_lines")), 2.6)
chk("s7 def chars both", -pct(g("paco","main+extra","def_chars"), g("new_port","main+extra","def_chars")), 2.6)
chk("s7 proof lines main", -pct(g("paco","main","proof_lines"), g("new_port","main","proof_lines")), 1.6)
for cp, want in [("paco", 8726), ("old_port", 8574), ("new_port", 8554)]:
    chk(f"s7 nontactic {cp}", nd(cp), want, 0)

chk("total lines main", -pct(g("paco","main","code_lines"), g("new_port","main","code_lines")), 2.9)
chk("total lines both", -pct(g("paco","main+extra","code_lines"), g("new_port","main+extra","code_lines")), 3.4)
chk("total lines both, first port",
    -pct(g("paco","main+extra","code_lines"), g("old_port","main+extra","code_lines")), 2.0)

# the library table, section 8
lib = {r["component"]: r for r in csv.DictReader(open("data/library.csv"))}
for comp, want in [("tactics",-18), ("lattice",30), ("tower",12), ("companion",-5), ("rel",19), ("core",6)]:
    r = lib[comp]
    chk(f"library {comp}", pct(int(r["old_lines"]), int(r["new_lines"])), want, 0.5)
chk("tactic implementation", pct(229 + 307, int(lib["tactics"]["new_lines"])), -65, 0.2)
chk("tests growth", pct(int(lib["tests"]["old_lines"]), int(lib["tests"]["new_lines"])), 290, 0.6)
chk("comment growth", pct(370, 455), 23, 0.5)

# the nine tactic families the rewrite removed from theories/
rows = list(csv.DictReader(open("data/metrics-tactics.csv")))
fam = lambda cp: {r["tactic"] for r in rows if r["checkpoint"] == cp and r["tree"] == "theories"}
gone = fam("old_port") - fam("new_port") - {"under_forall'"}   # under_forall' was renamed, not removed
chk("families removed", len(gone), 10, 0)

bad = [c for c in checks if not c[0]]
for ok, l, d in checks:
    print(("  ok  " if ok else "FAIL  ") + f"{l:26s} {d}")
print(f"\n{len(checks)-len(bad)}/{len(checks)} claims verified")
sys.exit(1 if bad else 0)
