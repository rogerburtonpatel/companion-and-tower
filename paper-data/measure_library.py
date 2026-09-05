#!/usr/bin/env python3
"""Tactic size of the two coinduction libraries, OCaml included.

    ./measure_library.py

Reports every line that exists to implement tactics, in four categories:

  ltac        every Ltac and Tactic Notation in theories/
  ocaml       the plugin sources, hand-written only
  ocaml_glue  the Rocq side that exists solely to feed the plugin: the reified
              syntax it consumes, the Register declarations that expose Rocq
              constants to it, and the Declare ML Module that loads it
  build       loadpath and packaging lines for the plugin

Writes library.csv next to this file.
"""
import csv, os, re, subprocess, sys, tempfile, shutil, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))

spec = importlib.util.spec_from_file_location("measure", os.path.join(HERE, "measure.py"))
M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)

LIBRARIES = [
    ("released",  os.path.join(ROOT, "pous-coinduction"),      "ac51c83"),
    ("rewritten", os.path.join(ROOT, "companion-and-tower"),   "HEAD"),
]

# reification_g.ml is generated from the .mlg, so it is not hand-written.
OCAML_EXT = (".ml", ".mli", ".mlg", ".mlpack")
GENERATED = ("reification_g.ml",)


def size(text):
    """Non-blank lines and their characters, comments removed. OCaml and Rocq
    share the (* *) comment syntax, so one stripper serves both."""
    text = M.strip_comments(text)
    ls = [l.strip() for l in text.split("\n")]
    ls = [l for l in ls if l]
    return len(ls), sum(len(l) for l in ls)


def materialise(work, tag, repo, rev):
    dest = os.path.join(work, tag)
    os.makedirs(dest, exist_ok=True)
    p = subprocess.run(["git", "-C", repo, "archive", rev],
                       check=True, stdout=subprocess.PIPE)
    subprocess.run(["tar", "xf", "-", "-C", dest], input=p.stdout, check=True)
    return dest


def ltac(base):
    """Every tactic definition in theories/, measured whole."""
    lines = chars = n = 0
    for f in sorted(os.listdir(os.path.join(base, "theories"))):
        if not f.endswith(".v"):
            continue
        for _, _, _, text in M.tactic_defs(os.path.join(base, "theories", f)):
            l, c = M.measure(text)
            lines += l; chars += c; n += 1
    return n, lines, chars


def ocaml(base):
    src = os.path.join(base, "src")
    if not os.path.isdir(src):
        return 0, 0, 0
    lines = chars = n = 0
    for f in sorted(os.listdir(src)):
        if not f.endswith(OCAML_EXT) or f in GENERATED:
            continue
        l, c = size(open(os.path.join(src, f), errors="replace").read())
        lines += l; chars += c; n += 1
    return n, lines, chars


def glue(base):
    """Rocq lines that exist only because the plugin does."""
    lines = chars = 0
    p = os.path.join(base, "theories", "tactics.v")
    if not os.path.exists(p):
        return 0, 0
    src = open(p, errors="replace").read()
    # the reified syntax the plugin consumes
    m = re.search(r"^Module reification\.$.*?^End reification\.$", src,
                  re.S | re.M)
    if m:
        l, c = size(m.group(0)); lines += l; chars += c
    # the constants exposed to it, and the command that loads it
    for line in M.strip_comments(src).split("\n"):
        s = line.strip()
        if s.startswith("Register ") or s.startswith("Declare ML Module"):
            lines += 1; chars += len(s)
    return lines, chars


def build(base):
    lines = chars = 0
    for name in ("_RocqProject", "_CoqProject"):
        p = os.path.join(base, name)
        if not os.path.exists(p):
            continue
        for line in open(p, errors="replace"):
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            if re.search(r"(^-I\s|src/|generate-meta-for-package)", s):
                lines += 1; chars += len(s)
    return lines, chars


def main():
    rows, work = [], tempfile.mkdtemp()
    try:
        for tag, repo, rev in LIBRARIES:
            base = materialise(work, tag, repo, rev)
            n, ll, lc = ltac(base)
            fn, ol, oc = ocaml(base)
            gl, gc = glue(base)
            bl, bc = build(base)
            rows.append({"library": tag, "revision":
                         subprocess.run(["git", "-C", repo, "rev-parse", "--short", rev],
                                        capture_output=True, text=True).stdout.strip(),
                         "tactic_defs": n,
                         "ltac_lines": ll, "ltac_chars": lc,
                         "ocaml_files": fn, "ocaml_lines": ol, "ocaml_chars": oc,
                         "glue_lines": gl, "glue_chars": gc,
                         "build_lines": bl, "build_chars": bc,
                         "total_lines": ll + ol + gl + bl,
                         "total_chars": lc + oc + gc + bc})
    finally:
        shutil.rmtree(work, ignore_errors=True)

    with open(os.path.join(HERE, "library.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)

    a, b = rows
    w1 = 26
    print(f"\n{'':{w1}}{'released':>12}{'rewritten':>12}{'change':>12}\n" + "  " + "-" * 60)
    for label, k in [("Ltac and Tactic Notation", "ltac_lines"),
                     ("OCaml plugin", "ocaml_lines"),
                     ("OCaml glue in Rocq", "glue_lines"),
                     ("plugin build config", "build_lines"),
                     ("TOTAL lines", "total_lines"),
                     ("TOTAL characters", "total_chars")]:
        d = "" if not a[k] else f"{100*(b[k]-a[k])/a[k]:+.0f}%"
        sep = "  " + "-" * 60 + "\n" if label.startswith("TOTAL lines") else ""
        print(f"{sep}  {label:{w1-2}}{a[k]:>12,}{b[k]:>12,}{d:>12}")
    print(f"\n  tactic definitions        {a['tactic_defs']:>12}{b['tactic_defs']:>12}")
    print(f"  wrote {os.path.join(HERE,'library.csv')}")


if __name__ == "__main__":
    main()
