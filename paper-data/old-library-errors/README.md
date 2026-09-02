# Error messages the released library produced

Each file states a goal the released `rocq-coinduction` rejects and the
rewritten library accepts. They exist to be compiled and screenshotted, not to
pass.

The released library is the `pous-coinduction` checkout at `ac51c83`, which
carries the OCaml reification plugin in `src/`.

```
rocq compile \
  -Q ../../../pous-coinduction/theories Coinduction \
  -I ../../../pous-coinduction/src \
  gfp_in_premise.v
```

| file | released library | rewritten library |
|---|---|---|
| `gfp_in_premise.v` | `Error: No such section variable or assumption: R.` | accepted |

The message names `R`, the candidate the user just wrote, which reads as though
the user's own script is at fault rather than the goal shape being unsupported.
The real cause is that the plugin's goal recogniser does not accept a fixed
point outside the conclusion.

Live instance: `theories/Eq/Eqit.v:575` of InteractionTrees at `d34881b`
(branch `new-coinduction`), in the proof of `eqit_Proper_R`.
