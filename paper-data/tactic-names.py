#!/usr/bin/env python3
"""List the tactic names defined in each state's theories tree, and diff them.

Names come from the same definition lines that collect.sh counts. For [Ltac] the
name is the identifier. For [Tactic Notation] the name is the sequence of quoted
tokens, which is what a user actually types, so "step" "in" becomes `step in`.
"""
import os, re, sys, subprocess, tempfile, shutil

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser(
    "~/home/learning-sandbox/learning/rocq/coinduction")
ITREES = os.path.join(ROOT, "InteractionTrees")
PACO   = os.path.join(ROOT, "itrees-old/InteractionTrees")

DEF = re.compile(r'^[ \t]*(?:#\[[a-z]*\][ \t]*)?(?:Global[ \t]+)?(Ltac|Tactic Notation)[ \t]+(.*)$')
IDENT = re.compile(r'([A-Za-z_][A-Za-z_0-9\']*)')
QUOTED = re.compile(r'"([^"]*)"')

def name_of(kind, rest):
    if kind == "Ltac":
        m = IDENT.match(rest.strip())
        return m.group(1) if m else None
    toks = QUOTED.findall(rest)
    return " ".join(toks) if toks else None

def names(base):
    out = {}
    for root, _, fs in os.walk(base):
        for f in sorted(fs):
            if not f.endswith(".v"): continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, base)
            for line in open(p, errors="replace"):
                m = DEF.match(line)
                if not m: continue
                n = name_of(m.group(1), m.group(2))
                if n: out.setdefault(n, set()).add(rel)
    return out

work = tempfile.mkdtemp()
try:
    def materialise(tag, repo, rev):
        d = os.path.join(work, tag); os.makedirs(d)
        if rev == "WORKTREE":
            shutil.copytree(os.path.join(repo, "theories"), os.path.join(d, "theories"))
        else:
            subprocess.run(f"git -C {repo} archive {rev} theories | tar xf - -C {d}",
                           shell=True, check=True)
        return names(os.path.join(d, "theories"))

    A = materialise("A", PACO,   "WORKTREE")
    B = materialise("B", ITREES, "d34881b")
    C = materialise("C", ITREES, "WORKTREE")

    def show(title, keys, src):
        print(f"\n## {title}  ({len(keys)})")
        for k in sorted(keys, key=str.lower):
            print(f"  {k:<28} {', '.join(sorted(src[k]))}")

    print(f"distinct tactic names: A(paco)={len(A)}  B(old lib)={len(B)}  C(new lib)={len(C)}")
    show("added by the port to enhanced coinduction (in B, not in A)", set(B) - set(A), B)
    show("removed by the library rewrite (in B, not in C)", set(B) - set(C), B)
    show("added by the library rewrite (in C, not in B)", set(C) - set(B), C)
    show("net new versus paco (in C, not in A)", set(C) - set(A), C)
    show("gone since paco (in A, not in C)", set(A) - set(C), A)
finally:
    shutil.rmtree(work)

# appended: full listing of the paco baseline, for categorising
