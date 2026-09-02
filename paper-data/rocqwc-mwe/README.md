Three files that reproduce the `rocq wc` misclassification. None needs to be
compiled; `rocq wc` is a standalone lexer over the file text.

    rocq wc overcount.v undercount-control.v undercount.v

`undercount-control.v` is the control. It differs from `undercount.v` by one
binder and `rocq wc` classifies it correctly, which is what isolates the bug.

| file | correct | `rocq wc` reports |
|---|---|---|
| `overcount.v` | spec 4, proof 0 | **spec 1, proof 3** |
| `undercount-control.v` | spec 2, proof 3 | spec 2, proof 3 |
| `undercount.v` | spec 2, proof 3 | **spec 5, proof 0** |

`overcount.v` contains no `Proof.`, no `Qed.` and no tactic. Renaming its
imported module from `MyDefinition` to `MyThing`, and changing nothing else,
gives the correct spec 4, proof 0.

See ../rocqwc-unsound.md for the diagnosis.
