# Data for the CPP writeup

Everything here is reproducible from the checkouts alone. Nothing modifies a
working tree.

```
./collect.sh > data.csv     # all size and tactic-surface tables
./run-probes.sh             # compiles probes.v; exit 0 means every claim holds
```

`data.csv` in this directory is the output of `collect.sh` at the time of
writing.

## The states being compared

The comparison has three states of InteractionTrees and two of the coinduction
library. `collect.sh` materialises each one into a temporary directory, from a
git object or by copying a working tree, and measures it there.

| id | what | where |
|----|------|-------|
| A | InteractionTrees on paco | `itrees-old/InteractionTrees`, branch `master`, `bd356ec` |
| A' | the same upstream content merged into our fork | `InteractionTrees` at `68b3568` |
| B | ported to enhanced coinduction, against `rocq-coinduction 1.21` | `InteractionTrees` at `d34881b` |
| C | ported to enhanced coinduction, against the rewritten library | `InteractionTrees` working tree |
| D | the library `rocq-coinduction 1.21` ships | `companion-and-tower` at `3dd5df7`, "Bare pous library" |
| D' | pristine upstream, an independent copy of the same | `pous-coinduction` working tree |
| E | the rewritten library | `companion-and-tower` working tree |

A and A' are measured separately on purpose. They are different commits in
different repositories, and they come out identical on every column, which is
the check that the extraction method is not perturbing anything. D and D' are
the same check for the library.

## How each number is obtained

**Size.** `rocq wc` over every `.v` file in the tree, summed. `rocq wc` reports
three counts per file: `spec` for lines of definitions, statements and
notations, `proof` for lines inside a proof, and `comments`. The summing
excludes the `total` line that `rocq wc` prints once per invocation. That matters
because `xargs` splits long file lists into several invocations, so a naive sum
counts every batch twice; the first version of this script did exactly that and
reported roughly double.

`spec` and `proof` are the interesting split for the argument, since the claim
under test is that enhanced coinduction shortens proofs. `comments` is reported
separately rather than folded in.

Table 4 also gives plain `wc -l` for comparison, because the two disagree in
direction and a reader will want to know which is being quoted. `rocq wc` ignores
blank lines, and there are about 2 700 of them in `theories`.

**Tactic surface.** The number of `Ltac` and `Tactic Notation` definitions,
counted by

```
grep -rhE '^[[:space:]]*(#\[[a-z]*\][[:space:]]*)?(Ltac|Tactic Notation)[[:space:]]' --include='*.v'
```

This is a line count, so a tactic whose definition spans several lines counts
once, and a `Tactic Notation` for the `in` variant of a tactic counts as its own
definition, which is the right unit here since each is a separate thing a user
has to know about.

**paco tokens** counts lines mentioning `paco<n>`, `gpaco<n>`, `pcofix` or
`gcofix`. It is a proxy for how much arity-indexed machinery is in use, not a
count of distinct identifiers.

**The OCaml plugin** is measured with `wc -l` over the `src/` tree at `3dd5df7`,
which is where the reification plugin lived before the rewrite removed it.

## What the numbers say

Cited by table and row in `data.csv`.

**The port from paco to enhanced coinduction cut proofs and grew definitions.**
Across `theories` and `extra`, proof lines fell by 754 and specification lines
rose by 333 (table 7, rows `both proof` and `both spec`, column `A->B`). Counting
comments as well, the two trees together changed by −18 lines, which is flat
(table 7, `both incl comments`). By plain `wc -l` the same change is +29 lines
(table 4). Either way the headline is that a 754-line reduction in proof was
almost entirely paid back elsewhere.

**The tactic surface nearly doubled.** `theories` went from 77 tactic definitions
on paco to 141 on enhanced coinduction, and `extra` from 35 to 82 (table 7, last
two rows, column `A->B`). This is the opposite of the expected direction, and it
is the concrete form of "workarounds for missing or insufficient tactics".

**The library rewrite took back 36 of those.** `theories` went from 141 to 105
(table 7, column `B->C`). Table 5 attributes the change: `Basics/Utils.v` −16,
`Eq/Rutt.v` −10, `Eq/Eqit.v` −8, `Core/KTreeFacts.v` −2. `extra` is unchanged at
82, because its tactics are per-development rather than re-implementations of the
library.

**The rewrite also pushed specification below the paco baseline.** `theories`
spec was 4 773 on paco, 4 849 on the old library, and 4 725 on the new one
(table 7, `theories spec`). So the definitional overhead the port introduced is
gone, and then some.

**The library grew, and deleted a plugin.** Excluding the test file at both ends,
the library went from 1 403 to 1 502 `spec+proof` lines, which is +7%, and from
15 to 45 tactic definitions (table 2), while removing 307 lines of OCaml
(table 3). Counting the plugin against it, 1 710 to 1 502 is −12%. Whole-system
the Rocq plus OCaml total went from 22 147 to 21 789 lines, which is −1.6%
(table 6).

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

- The three InteractionTrees states do not have identical file sets. A has 68
  files under `theories`, B and C have 65. Files were deleted during the port,
  including `Eq/Paco2.v`. The totals are therefore whole-tree totals, not a
  per-file matched comparison.
- `extra` is unchanged between B and C except for 10 proof lines, because the
  port to the new library touched it only where the old one broke. It is included
  because leaving it out would flatter the result.
- Timing is not measured here. Build time would be a fair thing to report and is
  not in this data set.
