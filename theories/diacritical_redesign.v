(** * Diacritical redesign experiment (autonomous session)

    GOAL.  In [experiments.v] we showed:
    - [f_below_w]: to certify [f] as a sound ACTIVE up-to technique ([f <= w]) it
      suffices (taking the strong partner [s := bot]) to prove two [f]-laws:
        (P) [evolution p f f]      i.e. [f ° b1 <= b1 ° f]   -- f is b1-COMPATIBLE
        (A) [r_evolution p a f f]  i.e. conditional b2-evolution.
    - The blocker for the "prove active up-to by tower induction" vision is that
      (P) is COMPAT-strength, strictly stronger than "[f <= t b1]" (up-to
      strength), and tower induction only validates at up-to strength.

    THIS FILE tests whether the passive law (P) can be RELAXED to [f <= t b1]
    while keeping [f] a sound active technique -- i.e. whether a tower-native
    diacritical companion exists.

    FINDING (this session): NO -- and the obstruction is structural, not about
    compat-vs-≤t strength.  The active law's conditional premise [R ↣ₚ R] is a
    b1-POST-fixpoint condition ([R <= b1 R], i.e. [R <= gfp b1]): it selects
    relations BELOW the gfp (bisimulation candidates).  Tower induction lives on
    the opposite side -- its chain elements are PRE-fixpoints ([b `x <= `x],
    i.e. ABOVE the gfp) -- and [ptower]'s relativiser [Q] must be MONOTONE
    (up-closed), so it can never supply a post-fixpoint premise.  The two sides
    meet only at [gfp].  Consequences, all checked below:
      - [active_premise_forces_fixpoint]: the premise on a chain element forces a
        b1-fixpoint (so it essentially never holds mid-chain);
      - [w_in_tower_b2_stalls]: tower induction for [w `x <= `x] stalls at exactly
        [b2 `x <= b1 (b2 `x)], and [ptower] cannot patch it.

    So there is NO tower-native diacritical companion that keeps the extra active
    power: that power comes precisely from the post-fixpoint conditional law,
    which is a COINDUCTION-side object, not a tower-induction-side one.  The
    realizable design is the complementary one:
      - use ordinary tower induction (validates/uses the ordinary up-to [t b']);
      - at an active position, SWAP to coinduction via [di_coinduction]
        ([experiments.v]) -- a single lemma application -- to get [w].
    The swap is necessary; the "even better" is a genuine impossibility. *)

(** UPDATE (later session): the impossibility above is specifically about a
    FIRST-ORDER tower on the base lattice [X].  It does NOT rule out a tower on
    the PAIR lattice [L_lift X].  In fact the diacritical companion [(u,w)] is a
    [di_similarity] of the two evolution progressions on [L_lift X], hence a gfp
    of a monotone SECOND-ORDER operator [B_di] -- see [experiments.v]:
    [B_di], [compan_gfp] ([compan == gfp B_di]), [B_di_spec], and the resulting
    tower-induction principles [di_chain_ind] / [di_tower].  The post-fixpoint
    guard [R <= b1 R] that blocks the first-order tower becomes a harmless fixed
    side-condition inside [B_di] (it does not mention [B_di]'s argument, so
    monotonicity survives).  So: no first-order base-lattice tower, but a genuine
    SECOND-order pair-lattice tower -- which is the honest "tower induction based
    on the diacritical companion". *)

From Stdlib Require Import Utf8 Setoid Morphisms.
Require Import lattice progress evolution companion diacritical_companion.
Require Import tactics tower rel utils.

Section redesign.
Context {X : Type} {CL : CompleteLattice X}.
Variable b1 b2 : mon X.

Notation p := (progress_mon b1).
Notation a := (progress_mon b2).
#[local] Instance PP1 : Progress (progress_mon b1) := progress_mono b1.
#[local] Instance PP2 : Progress (progress_mon b2) := progress_mono b2.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (a R S) (at level 70).

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).
Notation w := (snd compan).
Notation "` x" := (elem x) (at level 2).

(* ------------------------------------------------------------------------- *)
(** ** Experiment 1: why [ptower] cannot supply the active law's premise.

    [ptower] relativises tower induction by a MONOTONE (up-closed) predicate [Q]:
    its proof pushes [Q] down the chain using [b `x <= `x] ([b_chain]) together
    with [Q]'s monotonicity.  So any usable [Q] must be up-closed.

    But the active obligation [aev_weak]/[r_evolution] fires only under the
    premise [R ↣ₚ R], i.e. [R <= b1 R] -- a POST-fixpoint (down-closed) condition.
    On a chain element it collides with [b_chain]: *)

(* chain elements are b1-PRE-fixpoints *)
Remark chain_is_prefix (x : Chain b1) : b1 `x <= `x.
Proof. apply b_chain. Qed.

(* so the active premise [`x ↣ₚ `x] forces [`x] to be a b1-FIXPOINT -- and in the
   chain the only such elements sit at the very bottom (around [gfp b1]).  The
   premise is therefore essentially never available mid-chain. *)
Remark active_premise_forces_fixpoint (x : Chain b1) :
  `x ↣ₚ `x -> b1 `x == `x.
Proof.
  intro H. apply antisym.
  - apply b_chain.
  - exact H.
Qed.

(* [`x ↣ₚ `x] is a post-fixpoint predicate: NOT [Proper (leq ==> leq)], so it
   cannot be [ptower]'s [Q].  (If it were monotone, [x <= y] with [x <= b1 x]
   would give [y <= b1 y] -- false: take [y := top].)  Plain tower induction on
   [Chain b2] then stalls exactly here, as in [experiments.v]'s
   [w_in_tower_b'_rev]: the step needs [b2 `x <= b1 (b2 `x)], unavailable. *)

Proposition w_in_tower_b2_stalls : forall x : Chain b2, w `x <= `x.
Proof.
  apply (tower (P := fun y => w y <= y)).
  - apply inf_closed_leq.
  - intros x IH.
    (* goal: [w (b2 `x) <= b2 `x] *)
    destruct (wcompan_a_compatible p a) as [Hw'].
    transitivity (b2 (w `x)).
    + apply (Hw' (b2 `x) `x).
      * (* PREMISE [b2 `x ↣ₚ b2 `x] = [b2 `x <= b1 (b2 `x)] -- a b1-post-fixpoint,
           unavailable: chain elements are b2-pre-fixpoints. *)
        admit.
      * unfold progress_mon; reflexivity.       (* [b2 `x <= b2 `x] *)
    + apply b2; exact IH.
Abort.
(* Same stall as over [Chain b'].  [ptower] cannot patch the [admit]: it would
   need [Q y := y <= b1 y] as the relativiser, which is NOT [Proper (leq==>leq)]
   ([active_premise...] shows why), so [ptower]'s monotone-[Q] discipline rejects
   it.  The active premise lives on the POST-fixpoint (below-gfp) side; the chain
   lives on the PRE-fixpoint (above-gfp) side; they meet only at [gfp]. *)

End redesign.
