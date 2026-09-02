# `rocq wc` misclassifies specification and proof

`rocq wc` reports three columns per file, `spec`, `proof` and `comments`. Both
of the first two are wrong on ordinary Rocq source, in both directions, and by
enough to change a conclusion. This note documents the two failures with minimal
reproducers and points at the lexer rules that cause them.

Measured with Rocq 9.1.1. The lexer is `rocq-core/tools/rocqwc.mll`.

## Failure 1: a file with no proof in it is reported as mostly proof

`rocqwc.mll` matches the keywords `Definition`, `Fixpoint` and `Instance` at any
position in the token stream, rather than only at the head of a command. A
`Require` whose module path contains one of those words as a substring therefore
opens the lexer's `definition` state. That state looks for a `:=` before the next
`.` to decide the command was a definition. It does not find one, because the
command was a `Require`, so it concludes a proof has begun and counts everything
up to the next closer as proof.

`rocqwc-mwe/overcount.v` is five lines, three of which are definitions, and it
contains no `Proof.`, no `Qed.` and no tactic:

```coq
Require Import Foo.MyDefinition.

Definition a := 0.
Definition b := 1.
Definition c := 2.
```

```
$ rocq wc rocqwc-mwe/overcount.v
     spec    proof comments
        1        3        0
```

Three of the five lines are reported as proof. Renaming the module from
`MyDefinition` to `MyThing`, changing nothing else, gives the correct `spec 4, proof 0`.

This is not a contrived name. It fires on
`Require Export ITree.Core.ITreeDefinition.`, which appears throughout
InteractionTrees. `theories/Interp/Recursion.v` and `theories/Interp/Handler.v`
contain no proof at all, and `rocq wc` reports 62 proof lines in each.

## Failure 2: a proof is reported as specification

The same `definition` state accepts a `:=` anywhere before the closing `.`,
including inside parentheses. A statement carrying a local definition or a named
implicit argument in its binders therefore looks like a completed definition, the
lexer returns to specification, and the proof that follows is counted as
specification.

`rocqwc-mwe/undercount-control.v` and `rocqwc-mwe/undercount.v` differ in one
binder:

```coq
Instance foo (y : nat)                  : f nat 0 = 0.   (* control *)
Instance foo (y : nat) (z := f nat y)   : f nat 0 = 0.   (* affected *)
```

```
$ rocq wc rocqwc-mwe/undercount-control.v rocqwc-mwe/undercount.v
     spec    proof comments
        2        3        0 undercount-control.v
        5        0        0 undercount.v
```

The three-line proof disappears from the proof column entirely.

In InteractionTrees this fires on statements that take a chain argument carrying
a named implicit, such as

```coq
#[global] Instance eqit_secure_proper_chain
  ... (c : Chain (secure_eqit_mon (E := E) Label priv RR b1 b2 l)) : ...
```

`theories/Eq/Eqit.v` has 29 statements of that shape.

## Net effect

The two errors do not cancel. Across the InteractionTrees development `rocq wc`
overcounts proof by roughly 1500 lines at each of the three checkpoints we
measured.

## Confirming the diagnosis

The three files in `rocqwc-mwe/` are the evidence. Each is small enough to read
whole, and the control file differs from the affected one by a single binder,
which isolates the cause.

`measure.py` in this directory carries `split_sizes`, the corrected classifier
used for every figure we report. It follows the same intent as `rocqwc.mll`,
with the command keywords required at the head of a command and the `:=`
required at top level rather than at any bracket depth.

## Suggested fix

Both failures are in the same place. The keyword rules should anchor to the head
of a command, meaning after a `.` and any whitespace or attribute, rather than
matching anywhere in the token stream. The `:=` test should track bracket depth
and accept only a top-level occurrence.
