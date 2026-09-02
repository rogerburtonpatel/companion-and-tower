#!/usr/bin/env python3
"""Measure the three checkpoints of the InteractionTrees port.

Writes metrics.csv (one row per checkpoint per scope) and metrics-tactics.csv
(one row per counted tactic definition, so the count can be checked by hand).

    ./measure.py

Nothing here modifies a working tree. Each checkpoint is copied into a
temporary directory first.

The only input that requires judgement is the tactic list below. Everything
after it is counting.
"""

import csv, os, re, shutil, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(ROOT)                      # .../coinduction
ITREES = os.environ.get("ITREES") or os.path.join(ROOT, "InteractionTrees")
PACO   = os.environ.get("PACO")   or os.path.join(ROOT, "itrees-old/InteractionTrees")

# Every checkpoint is a committed revision, so a branch switch in the source
# repository cannot change what is measured. PACO is a separate checkout whose
# master is the upstream paco tree.
CHECKPOINTS = [
    ("paco",     PACO,   "bd356ec"),    # ITrees on paco, upstream master
    ("old_port", ITREES, "d34881b"),    # branch new-coinduction: ported against
                                        # the released rocq-coinduction
    ("new_port", ITREES, "cpp"),        # branch cpp: ported against the
                                        # rewritten library
]
TREES = ["theories", "extra"]


# ===========================================================================
# THE TACTIC LIST
#
# Tactics that exist only to drive the coinduction library, whichever library
# that is at this checkpoint. This is what "tactic surface" means: the Ltac a
# development has to write to make its coinduction library usable.
#
#   "name a user types": [every definition that implements it]
#
# The count of distinct tactics is the number of keys. Lines and characters
# count every definition in every list, including duplicates across files,
# which is how duplication shows up in the numbers.
#
# NOT counted, at every checkpoint, because a development would need them
# whatever it was built on:
#   sinv, simpobs_subst, apply_foralls, solve_eqitF, taul, taur, taus,
#   genret, gentau, genvis, auto_ctrans, by_coinduction, pi_solve
#
# eret/etau/evis/ebind are the euttG combinators at paco and are counted there.
# The ports reuse those names for plain constructor shortcuts that have nothing
# to do with coinduction, so they are not counted at the two later checkpoints.
# ===========================================================================

TACTICS = {

  "paco": {
    "pcofix":         ["pcofix", "pcofix_", "pcofix_with", "apply_paco_acc"],
    "gpaco":          ["gpaco", "gpaco_"],
    "ecofix":         ["ecofix"],
    "einit":          ["einit"],
    "efinal":         ["efinal"],
    "ebase":          ["ebase"],
    "eret":           ["eret"],
    "etau":           ["etau"],
    "evis":           ["evis"],
    "estep":          ["estep"],
    "ebind":          ["ebind"],
    "edrop":          ["edrop"],
    "gfinal_with":    ["gfinal_with"],
    "pmonauto_itree": ["pmonauto_itree"],
    "unfold_eqit":    ["unfold_eqit"],
    "fold_eqitF":     ["fold_eqitF"],
    "unfold_rutt":    ["unfold_rutt"],
    "fold_ruttF":     ["fold_ruttF"],
    "fold_eutt":      ["fold_eutt"],
    "fold_secure":    ["fold_secure"],
    # apply_paco_acc is defined twice, once behind pcofix and once behind
    # ecofix. It is listed under pcofix; both definitions are measured.
  },

  "old_port": {
    "step":            ["step", "step in", "step_", "step_in"],
    "unstep":          ["unstep", "unstep in", "unstep_in"],
    "rstep":           ["rstep", "rstep in"],
    "runstep":         ["runstep", "runstep in"],
    "simple_step":     ["simple_step"],
    "coinduction":     ["coinduction"],
    "icoinduction":    ["icoinduction"],
    "tower induction": ["tower induction", "tower_induction", "clear_old_chain"],
    "monauto":         ["monauto", "apply_leq", "induct_on_premise"],
    "inf_closed_auto": ["inf_closed_auto", "inf_closed_final_auto",
                        "inf_closed_forall_auto", "inf_closed_impl_auto"],
    "to_mon":          ["to_mon", "to_mon in", "to_mon_core", "to_mon_in"],
    "to_rmon":         ["to_rmon", "to_rmon in", "to_rmon_core", "to_rmon_in"],
    "to_mon_s":        ["to_mon_s"],
    "iunfold":         ["iunfold", "iunfold in", "iunfold in *",
                        "iunfold_all", "iunfold_in"],
    "iunfold_coind":   ["iunfold_coind"],
    "runfold":         ["runfold", "runfold_in"],
    "fold_rutt":       ["fold_rutt", "fold_rutt_in"],
    "refold":          ["refold", "refold in", "refold_in"],
    "icbn":            ["icbn", "icbn in", "icbn in *", "icbn_in"],
    "rcbn":            ["rcbn", "rcbn in", "rcbn in *", "rcbn_in"],
    "bcbn":            ["bcbn"],
    "euttsimpl":       ["euttsimpl"],
    "under_forall'":   ["under_forall'"],
  },

  "new_port": {
    "step":         ["step", "step in"],
    "unstep":       ["unstep", "unstep in"],
    "rstep":        ["rstep", "rstep in"],
    "simple_step":  ["simple_step"],
    "coinduction":  ["coinduction"],
    "icoinduction": ["icoinduction"],
    "to_mon":       ["to_mon", "to_mon in", "to_mon_core", "to_mon_in"],
    "refold":       ["refold", "refold in", "refold_in"],
    "icbn":         ["icbn", "icbn in", "icbn in *", "icbn_in"],
    "rcbn":         ["rcbn", "rcbn in", "rcbn_in"],
    "bcbn":         ["bcbn"],
    "under_forall": ["under_forall"],
  },
}


# ===========================================================================
# Reading a .v file
# ===========================================================================

def strip_comments(src):
    """Blank out (* ... *) and "..." , keeping every character position."""
    out, i, depth, n = list(src), 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith('"', i):        # skip a string literal
            i += 1
            while i < n and not src.startswith('"', i):
                i += 1
            i += 1
        elif src.startswith("(*", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
        elif src.startswith("*)", i) and depth:
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
        else:
            if depth and src[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def end_of_command(clean, start):
    """Index just past the '.' that closes the command beginning at start.

    A '.' closes a command only at bracket depth zero and when followed by
    whitespace or end of file, so qualified names like ITree.Core do not end
    one."""
    depth, i, n = 0, start, len(clean)
    while i < n:
        c = clean[i]
        if c == '"':                       # a '.' inside a string ends nothing
            i += 1
            while i < n and clean[i] != '"':
                i += 2 if clean[i] == "\\" else 1
            i += 1
            continue
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1                     # <= 0 below: tolerate notation
        elif c == "." and depth <= 0 and (i + 1 >= n or clean[i + 1] in " \t\r\n"):
            return i + 1
        i += 1
    return n


def commands(clean):
    """Yield (start, end) for each top-level command."""
    i, n = 0, len(clean)
    while i < n:
        if clean[i] in " \t\r\n":
            i += 1
            continue
        end = end_of_command(clean, i)
        yield i, end
        i = end


def measure(text):
    """Lines and characters, comments already gone, blank lines dropped."""
    ls = [l.strip() for l in text.split("\n")]
    ls = [l for l in ls if l]
    return len(ls), sum(len(l) for l in ls)


# ===========================================================================
# Finding tactic definitions
# ===========================================================================

ATTRIBUTE = re.compile(r'#\[[^\]]*\]\s*')
MODIFIERS = ("Global", "Local", "Polymorphic", "Monomorphic", "Cumulative",
             "NonCumulative", "Private", "Program", "Existing")


def head(cmd):
    """The command with attributes and modifiers stripped from the front."""
    s = cmd.lstrip()
    while True:
        m = ATTRIBUTE.match(s)
        if m:
            s = s[m.end():]
            continue
        for w in MODIFIERS:
            if re.match(re.escape(w) + r"\b", s):
                s = s[len(w):].lstrip()
                break
        else:
            return s


def defined_name(cmd):
    """(kind, name) if this command defines a tactic, else None.

    'Ltac foo :=' gives foo. 'Tactic Notation "step" "in" ident(h)' gives
    'step in', which is what a user types."""
    s = head(cmd)
    m = re.match(r'Ltac\s+([A-Za-z_][A-Za-z0-9_\']*)', s)
    if m:
        return "Ltac", m.group(1)
    if re.match(r'Tactic\s+Notation\b', s):
        words = re.findall(r'"([^"]*)"', s[:s.find(":=") if ":=" in s else len(s)])
        if words:
            return "Tactic Notation", " ".join(words)
    return None


def tactic_defs(path):
    """Yield (line, kind, name, text) for every tactic definition in a file."""
    src = open(path, encoding="utf-8", errors="replace").read()
    clean = strip_comments(src)
    for start, end in commands(clean):
        got = defined_name(clean[start:end])
        if got:
            yield clean.count("\n", 0, start) + 1, got[0], got[1], clean[start:end]


# ===========================================================================
# Splitting specification from proof
# ===========================================================================

PROOF_START = ("Theorem", "Lemma", "Fact", "Remark", "Goal", "Correctness",
               "Corollary", "Proposition", "Property", "Example",
               "Next Obligation", "Obligation")
DEF_START = ("Definition", "Fixpoint", "CoFixpoint", "Instance")
CLOSER = re.compile(r'\b(Qed|Defined|Save|Abort|Admitted)\b[^.]*\.')


def opens_proof(cmd):
    """A statement opens a proof, and so does a Definition given by tactics
    rather than by a top-level ':='."""
    s = head(cmd)
    if any(re.match(re.escape(k) + r"\b", s) for k in PROOF_START):
        return True
    if not any(re.match(re.escape(k) + r"\b", s) for k in DEF_START):
        return False
    depth = 0                                  # ':=' must be at top level
    for i, c in enumerate(cmd):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and cmd[i:i + 2] == ":=":
            return False
    return True


def split_sizes(path):
    """(def_lines, proof_lines, def_chars, proof_chars, code_lines) for a file.

    def_lines and proof_lines both count a line that carries a statement and
    its proof, so they overshoot the file. code_lines is every non-blank
    comment-free line counted once, which is the honest total."""
    clean = strip_comments(open(path, encoding="utf-8", errors="replace").read())
    proof = bytearray(len(clean))              # 1 where the text is proof
    for start, end in commands(clean):
        if not opens_proof(clean[start:end]):
            continue
        m = CLOSER.search(clean, end)
        stop = m.end() if m else len(clean)
        for j in range(end, stop):
            proof[j] = 1

    # A line is examined between its first and last non-space character, so
    # indentation never decides anything. A line carrying both a statement and
    # its proof counts once in each column, and its characters are split
    # between them.
    dl = pl = dc = pc = cl = 0
    pos = 0
    for line in clean.split("\n"):
        a = len(line) - len(line.lstrip())
        b = len(line.rstrip())
        if b <= a:                             # blank line, counts for neither
            pos += len(line) + 1
            continue
        d = sum(1 for k in range(a, b) if not proof[pos + k])
        p = (b - a) - d
        if d:
            dl += 1
            dc += d
        if p:
            pl += 1
            pc += p
        cl += 1
        pos += len(line) + 1
    return dl, pl, dc, pc, cl


# ===========================================================================
# Running it
# ===========================================================================

def materialise(work, tag, repo, rev):
    """Copy one checkpoint into a temp directory. Never touches the source."""
    dest = os.path.join(work, tag)
    os.makedirs(dest, exist_ok=True)
    for tree in TREES:
        if rev == "WORKTREE":
            shutil.copytree(os.path.join(repo, tree), os.path.join(dest, tree))
        else:
            p = subprocess.run(["git", "-C", repo, "archive", rev, tree],
                               check=True, stdout=subprocess.PIPE)
            subprocess.run(["tar", "xf", "-", "-C", dest],
                           input=p.stdout, check=True)
    return dest


def vfiles(base):
    for tree in TREES:
        for d, _, fs in os.walk(os.path.join(base, tree)):
            for f in sorted(fs):
                if f.endswith(".v"):
                    p = os.path.join(d, f)
                    yield tree, os.path.relpath(p, base), p


def main():
    rows, audit, missing = [], [], []
    work = tempfile.mkdtemp()
    try:
        for label, repo, rev in CHECKPOINTS:
            base = materialise(work, label, repo, rev)
            wanted = {name: family
                      for family, names in TACTICS[label].items()
                      for name in names}
            seen = set()
            size = {t: [0, 0, 0, 0, 0] for t in TREES}  # dl, pl, dc, pc, cl
            tac = {t: [0, 0] for t in TREES}           # lines, chars
            fams = {t: set() for t in TREES}

            for tree, rel, path in vfiles(base):
                for k, v in enumerate(split_sizes(path)):
                    size[tree][k] += v
                for line, kind, name, text in tactic_defs(path):
                    if name not in wanted:
                        continue
                    seen.add(name)
                    lines, chars = measure(text)
                    tac[tree][0] += lines
                    tac[tree][1] += chars
                    fams[tree].add(wanted[name])
                    audit.append([label, tree, rel, line, kind, name,
                                  wanted[name], lines, chars])

            for name in set(wanted) - seen:
                missing.append(f"{label}: {name}")

            for scope, trees in [("main", ["theories"]), ("main+extra", TREES)]:
                rows.append({
                    "checkpoint": label, "scope": scope,
                    "library_tactics": len(set().union(*(fams[t] for t in trees))),
                    "tactic_lines": sum(tac[t][0] for t in trees),
                    "tactic_chars": sum(tac[t][1] for t in trees),
                    "def_lines":    sum(size[t][0] for t in trees),
                    "proof_lines":  sum(size[t][1] for t in trees),
                    "def_chars":    sum(size[t][2] for t in trees),
                    "proof_chars":  sum(size[t][3] for t in trees),
                    "code_lines":   sum(size[t][4] for t in trees),
                })
    finally:
        shutil.rmtree(work, ignore_errors=True)

    if missing:
        sys.exit("the tactic list names definitions that do not exist:\n  "
                 + "\n  ".join(sorted(missing)))

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "metrics.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    with open(os.path.join(here, "metrics-tactics.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["checkpoint", "tree", "file", "line", "kind", "definition",
                    "tactic", "lines", "chars"])
        w.writerows(audit)

    for r in rows:
        print(" ".join(f"{k}={v}" for k, v in r.items()))


if __name__ == "__main__":
    main()
