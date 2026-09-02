# Data for the CPP writeup

Everything here is reproducible from the checkouts alone. Nothing modifies a
working tree.

```
./measure.py                # the headline table -> metrics.csv, metrics-tactics.csv
./run-probes.sh             # compiles probes.v; exit 0 means every claim holds
./collect.sh > data.csv     # the older, wider set of tables (see the warning below)
```

## The headline table

`metrics.csv` has one row per checkpoint per scope and nothing else:

```
checkpoint,scope,library_tactics,tactic_lines,tactic_chars,def_lines,proof_lines,def_chars,proof_chars
```

The three checkpoints are the same development at three points in its life.

| checkpoint | what | where |
|---|---|---|
| `paco` | InteractionTrees built on paco | `itrees-old/InteractionTrees` working tree |
| `old_port` | ported to enhanced coinduction, against `rocq-coinduction 1.21` | `InteractionTrees` at `d34881b` |
| `new_port` | ported to enhanced coinduction, against the rewritten library | `InteractionTrees` working tree |

The two scopes are separate data points because they behave differently.

| scope | what |
|---|---|
| `main` | `theories/` alone, the library proper |
| `main+extra` | `theories/` and `extra/` together, the whole Rocq development |

`extra/` holds the downstream developments built on the library: `IForest`,
`ITrace`, `Secure` and `Dijkstra`. Reporting only the union hides that the two
halves moved in opposite directions on tactic surface, so both are given.
Figures for `extra/` alone are the difference between the two rows, except
`library_tactics`, which counts distinct names and so cannot be subtracted.

Neither tree has a test directory. ITrees' `tests/` is a separate extraction
harness and is out of scope at all three checkpoints, as is the coinduction
library itself, which is measured separately in `data.csv` table 2.

### `library_tactics`

The count of distinct tactic names that exist only to drive the coinduction
machinery, whichever machinery that is at this checkpoint. Three conventions
make the number mean something:

- **The unit is the name a user types.** `step` and `step in` are one name.
- **A private helper folds into the name it serves.** `to_mon_core` is part of
  `to_mon`; `pcofix_`, `pcofix_with` and `apply_paco_acc` are part of `pcofix`.
  They still contribute their lines and characters.
- **A name defined in several files counts once.** `step` is defined five times
  at `old_port`; that duplication shows up in `tactic_lines`, not in the count.

Membership is the `TACTICS` table at the top of `measure.py`, which is curated by
hand, not pattern-matched, because a name-based scan gets this wrong in both
directions. `eret`, `etau`, `evis` and `ebind` are the `euttG` combinators at
`paco` and are counted; the port replaced them with constructor shortcuts of
the same names that would exist without any coinduction library, so at the two
later checkpoints the same names are not counted. The script fails loudly if
the table names a definition its tree does not have, so it cannot silently rot.

Also excluded at every checkpoint, as domain tactics that any development would
need: `sinv`, `simpobs_subst`, `apply_foralls`, `solve_eqitF`, `taul`, `taur`,
`taus`, `genret`, `gentau`, `genvis`, `auto_ctrans`, `by_coinduction`,
`pi_solve`.

`metrics-tactics.csv` lists every counted definition with its file, line,
tactic name, role and size, so the count can be vetted by hand. `role` splits
the tactics into `driver` (advances the proof: applies the coinduction
principle, takes a step, discharges a side condition) and `plumbing` (only
reshapes the goal so a driver will fire: unfolds an alias, folds one back,
re-observes a constructor argument, reduces a functor application).

### `tactic_lines` and `tactic_chars`

Every definition belonging to those names, every copy counted separately. The
extent of a definition is found by scanning to the `.` that closes it at
bracket depth zero and outside a string, so a multi-line `Ltac` is measured
whole.

### `def_lines`, `proof_lines`, `def_chars`, `proof_chars`

A line is counted after comments are removed and leading and trailing
whitespace is stripped; a line that is then empty is not counted. Characters
are the length of that stripped, comment-free line, so indentation does not
inflate the count but the spaces inside an expression do. A line that carries
both a statement and its proof counts once in each column, which is why the two
line columns can sum to slightly more than the file has lines.

## `rocq wc` is not sound enough to use here, and `data.csv` inherits that

`rocq wc` is the obvious tool for the specification/proof split and it gets
these files badly wrong. Its lexer, `rocq-core/tools/rocqwc.mll`, matches the
keywords `Definition`, `Fixpoint` and `Instance` at **any** position in the
token stream rather than at the head of a command. So the import line

```coq
Require Export ITree.Core.ITreeDefinition.
```

fires the `def_start` rule on the `Definition` inside `ITreeDefinition`, enters
the lexer's `definition` state, finds no `:=` before the next dot, and concludes
that a proof has begun. Everything to the next `Qed` is then counted as proof.
`theories/Interp/Recursion.v` and `theories/Interp/Handler.v` contain no proof
at all, no `Proof.` and no `Qed.`; `rocq wc` reports 62 proof lines in each.

The same lexer errs in the other direction. Its `definition` state accepts a
`:=` anywhere, including inside parentheses, so a statement with a named
argument such as

```coq
#[global] Instance eqit_secure_proper_chain
  ... (c : Chain (secure_eqit_mon (E := E) Label priv RR b1 b2 l)) : ...
```

returns the lexer to specification, and the 88-line proof that follows is
counted as specification. `theories/Eq/Eqit.v` has 29 statements of that shape.

Across the whole development the two errors do not cancel: `rocq wc`
overcounts proof by about 1 500 lines at each checkpoint.

`measure.py` uses a corrected classifier that requires the command keywords at
the head of a command and the `:=` at top level. The `rocq wc` bug itself is
written up separately in `rocqwc-unsound.md`, with minimal reproducers in
`rocqwc-mwe/`.

**Consequence for `data.csv`.** Its `spec` and `proof` columns come from
`rocq wc` and carry this error; its `spec+proof` totals, tactic counts, file
counts and the OCaml plugin table are unaffected. Quote `metrics.csv` for the
specification/proof split.

## What the numbers say

```
checkpoint  scope       library_tactics  tactic_lines  tactic_chars  def_lines  proof_lines  def_chars  proof_chars
paco        main                     16           118          4181       5870         6231     213716       176031
old_port    main                     21           240          8537       5820         6119     213284       160788
new_port    main                     12           108          3787       5635         6110     206507       160097
paco        main+extra               20           127          4586       8853        12018     354025       399700
old_port    main+extra               23           360         12754       8934        11521     355226       351873
new_port    main+extra               14           215          7586       8736        11502     348031       350379
```

**In the library proper the rewrite finishes below the paco baseline on every
tactic measure.** 16 tactics to 12, −25%; 118 lines to 108, −8.5%; 4 181
characters to 3 787, −9.4%. The port to enhanced coinduction first pushed all
three the wrong way, to 21 tactics and 8 537 characters, because the old
library's reification plugin did not cover ITrees' arity and ITrees
re-implemented stepping, inf-closedness and tower induction itself in two
places. The rewrite removed `iunfold`, `runfold`, `runstep`, `fold_rutt`,
`iunfold_coind`, `euttsimpl`, `inf_closed_auto`, `monauto` and
`tower induction` from `theories/` outright, the last three by making the
library's own versions reach the files that need them.

**Every remaining regression against paco lives in `extra/`.** Derived by
subtracting the two scopes, its tactic characters go 405 → 4 217 → 3 799, an
838% increase that the rewrite barely dented, against 9 → 120 → 107 lines. That
is why `main+extra` still reads +65% on characters while `main` reads −9%. Of
the 3 799 characters, 3 473 are one file: `extra/IForest.v` carries 19 `#[local]`
definitions that are a near-copy of the `Eq/Eqit.v` block, differing only by a
per-development list of aliases to unfold, pairs to fold, and constants to
`cbn`. Deduplicating that one file would bring `main+extra` close to the paco
baseline; nothing else in `extra/` is large.

**The proof reduction runs the other way.** `extra/` gained more than the
library proper: proof characters fell 14.9% there against 9.1% in `main`, and
proof lines 6.8% against 1.9%. So the developments that pay the most tactic
surface are also the ones that got the most proof back. Enhanced coinduction
helped the downstream users more than it helped the library, and cost them more
to adopt.

**Characters move about three times as far as lines.** Across `main+extra`,
proof lines fell 4.3% while proof characters fell 12.3%; in `main`, 1.9%
against 9.1%. Enhanced coinduction did not mainly delete proof lines, it made
the surviving lines shorter. A line count alone understates the effect by a
factor of three, which is the argument for reporting both.

**Specification is flat.** `main` definition lines fall 4.0% and characters
3.4%; across `main+extra`, 1.3% and 1.7%. The definitional overhead the port
introduced is gone, and then a little more.

## The states in `data.csv`

`collect.sh` predates `measure.py` and covers more ground: the coinduction
library itself, the deleted OCaml plugin, raw `wc -l`, and per-file tactic
deltas. It compares five states.

| id | what | where |
|----|------|-------|
| A | InteractionTrees on paco | `itrees-old/InteractionTrees`, branch `master`, `bd356ec` |
| A' | the same upstream content merged into our fork | `InteractionTrees` at `68b3568` |
| B | ported, against `rocq-coinduction 1.21` | `InteractionTrees` at `d34881b` |
| C | ported, against the rewritten library | `InteractionTrees` working tree |
| D | the library `rocq-coinduction 1.21` ships | `companion-and-tower` at `3dd5df7` |
| D' | pristine upstream, an independent copy of the same | `pous-coinduction` working tree |
| E | the rewritten library | `companion-and-tower` working tree |

A and A' are measured separately on purpose. They are different commits in
different repositories and come out identical on every column, which is the
check that the extraction method is not perturbing anything. D and D' are the
same check for the library.

**The library grew, and deleted a plugin.** Excluding the test file at both
ends, the library went from 1 403 to 1 502 `spec+proof` lines, +7%, and from 15
to 45 tactic definitions (table 2), while removing 307 lines of OCaml
(table 3). Counting the plugin against it, 1 710 to 1 502 is −12%.

Growth in the library is not evenly spread. The tactic implementation, meaning
`tactics.v` together with the plugin it called, went from 229 + 307 = 536 lines
to 227, a reduction of 58%. What grew is documentation and tests, which is
deliberate: comments went from 361 to 474 lines and `tests.v` from 84 to 336.

The honest summary is that the work moved machinery out of InteractionTrees and
into the library, and out of OCaml and into Rocq, shrinking the tactic
implementation by more than half while the library as a whole stayed about the
same size once its new tests and documentation are counted.

## Behavioural claims

`probes.v` states nine claims as Rocq goals and `run-probes.sh` compiles it.
Compilation succeeding is the evidence. The claims cover the fixpoint-in-a-premise
case that the plugin rejected, the arity at which `apply sub_bChain` does not
type, stepping through a definition that stands for a fixpoint, the candidate
name clashing with a binder of the goal, automatic inf-closedness for the
relation classes at that arity, and functor monotonicity by `monauto`.

## Caveats a reader should know

- The three states do not have identical file sets. `paco` has 68 files under
  `theories`, the other two have 65. Files were deleted during the port,
  including `Eq/Paco2.v`, whose 55 lines of `pcofix` reimplementation count
  against the paco checkpoint and vanish afterwards.
- `extra` is nearly unchanged between `old_port` and `new_port`, because the
  port to the new library touched it only where the old one broke. It is
  included because leaving it out would flatter the result.
- A tactic-surface count from grep needs a compile behind it. Three times in
  this work a name-based scan misled us: `intros !` is declared with a space and
  invoked without one 51 times, so grep found only its two definitions and
  called it dead; `eret`, `etau` and `evis` are the same names doing different
  jobs before and after the port; and a shell counter reported `bcbn` as unused
  when it has 50 uses. Every deletion here was confirmed by building.
- Timing is not measured. Build time would be a fair thing to report and is not
  in this data set.
