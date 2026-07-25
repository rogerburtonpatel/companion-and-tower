(** * Experiments: unifying the ordinary companion [t] with the diacritical
      companion [(u, w)].

   Everything here relates the single-function companion [t b] of a monotone
   function [b] to the diacritical companion [(u, w)] of a pair of progress
   relations, by *deriving* the progressions from monotone functions.

   - [Section pairs]: the collapsed case [p = a = progress_mon b].  Both
     diacritical components coincide with the ordinary companion: [u == t] and
     [w == t].
   - [Section diacritical_two]: two genuinely different progressions induced by
     [b1] (passive) and [b2] (active), combined as [b1 ⊓ b2].  Here [u] and [w]
     come apart and [w] escapes the combined companion. *)

From Stdlib Require Import Utf8 Setoid Morphisms.
Require Import lattice progress evolution companion diacritical_companion.
Require Import tactics.
Require Import utils. 

(* ========================================================================= *)
(* The collapsed case: a single [b], with both progressions induced by it. *)
Section pairs.
Context {X : Type} {CL : CompleteLattice X}.
Variable b : mon X.
Notation t := (t b).
Notation compat f := (f ° b <= b ° f) (only parsing).

(* Unify the theory: rather than taking [p], [a] as abstract progressions with a
   separate, unrelated [b] (and bolting them together with an [Hb] hypothesis),
   we *derive* both progressions from the monotone function [b] already in
   context.  [R ↣ S := R <= b S] is the progress relation induced by [b]
   ([progress_mon]/[progress_mono] from [progress.v]).  The diacritical
   companion [(u, w)] of [b] is then [compan p a] for [p = a = progress_mon b],
   and everything is stated over a single [b]. *)
Notation p := (progress_mon b).
Notation a := (progress_mon b).
Instance PP : Progress (progress_mon b) := progress_mono b.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (a R S) (at level 70).
Notation "f ↝ₚ g" := (p_evolution p f g) (at level 70).
Notation "f ↝ₐ g" := (a_evolution p a f g) (at level 70).

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).
Notation w := (snd compan).

(* With [p = a = progress_mon b] the connecting hypothesis is now definitional:
   [R ↣ₚ R ∧ R ↣ₐ R] is just [R <= b R], so the di-similarity of the pair is the
   greatest post-fixpoint of [b]. *)
Lemma di_similarity_gfp_eq : di_similarity p a == gfp b.
Proof.
  apply antisym.
  - (* di_similarity p a <= gfp b: each self-progressing R is a post-fixpoint. *)
    unfold di_similarity. apply sup_spec. intros R [HR _].
    apply leq_gfp. exact HR.
  - (* gfp b <= di_similarity p a: gfp b self-progresses in both p and a. *)
    apply leq_xsup. split; apply gfp_pfp.
Qed.

(* One step of the ordinary companion [t] respects the progress induced by [b]:
   this is just monotonicity of [t] followed by its compatibility [compat_t]. *)
Lemma t_step R S : R <= b S -> t R <= b (t S).
Proof.
  intro H. transitivity (t (b S)).
  - apply (Hbody t). exact H.
  - apply (compat_t b S).
Qed.

(* The passive companion [u] is below the ordinary companion [t]: [u] is
   compatible w.r.t. [b], using that [u] p-evolves to itself. *)
Lemma u_leq_t : u <= t.
Proof.
  apply leq_t. intro x.
  destruct (ucompan_p_compatible p a) as [Hu].
  apply (Hu (b x) x). unfold progress_mon. reflexivity.
Qed.

(* Conversely [(t, t)] is a compatible pair, so it lies below the diacritical
   companion [(u, w)].  This gives both [t <= u] and [t <= w]. *)
Lemma t_pair_compatible : compatible p a (t, t).
Proof.
  split.
  - (* p_evolution: t p-evolves to itself, in both components. *)
    split; constructor; intros R S H; apply t_step; apply H.
  - (* a_evolution. *)
    split.
    + (* aev_strong: t a-evolves to t. *)
      constructor. intros R S H. apply t_step, H.
    + (* aev_weak: t (p#a)-evolves to t. *)
      constructor. intros R S _ H. apply t_step, H.
Qed.

Lemma t_below_compan : (t, t) <= compan.
Proof. apply leq_xsup. exact t_pair_compatible. Qed.

(* Unification: the passive diacritical companion [u] coincides with the
   ordinary companion [t]. *)
Proposition u_t : u == t.
Proof.
  apply antisym.
  - apply u_leq_t.
  - apply (proj1 t_below_compan).
Qed.

Lemma t_leq_w : t <= w.
Proof. apply (proj2 t_below_compan). Qed.

(* In THIS (collapsed) setting [p = a = progress_mon b], the active companion
   also collapses to [t]: [pev_weak] independently forces [w ↝[p] w], i.e. [w]
   is fully [b]-compatible, so [w <= t] as well.  The diacritical pair is just
   [(t, t)].  The room for [w] to rise above [t] only opens up once the active
   progression genuinely differs from the passive one -- see [diacritical_two]. *)
Lemma w_leq_t : w <= t.
Proof.
  apply leq_t. intro x.
  destruct (wcompan_p_compatible p a) as [Hw].
  apply (Hw (b x) x). unfold progress_mon. reflexivity.
Qed.

Proposition w_t : w == t.
Proof. apply antisym; [ apply w_leq_t | apply t_leq_w ]. Qed.

End pairs.

(* ========================================================================= *)
(* The genuine diacritical setting: two DIFFERENT progressions, [p] induced by
   a passive [b1] and [a] induced by an active [b2].  The combined behaviour is
   [b := b1 ⊓ b2], and we probe how the diacritical companion [(u, w)] of
   [(p, a)] relates to the ordinary companions [t b1] (passive) and [t b]
   (combined).  This is where [u != w] and [w] escapes the combined companion. *)
Section diacritical_two.
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

(* we want tower induction on b2 for proving f is active up-to techniques *)
(* take (s, f) to be (⊥, f) for some f *)
(* obligations on s dispatched trivially *)
(* f needs to b1-evolve to f, and contitionally evolve to f. *)
(* then f is a sound up-to *)
(* can we embed these conditions in the tower *)

(* really, to prove any f is a sound up-to active technique, 
we should be able to do so by tower induction on b2's tower! 
this is because f need only be sound in active cases, 
and b2's tower is only active cases. 
*)

(* Setting the strong partner [s := bot] makes the two [s]-obligations
   ([pev_strong], [aev_strong]) trivial ([bot <= _]).  What remains is a clean
   SUFFICIENT condition for [f] to be a sound active up-to technique ([f <= w]):
   [f] must b1-evolve to itself and conditionally b2-evolve to itself. *)
Lemma f_below_w (f : [X ⇒ X])
  (Hp : evolution p f f)          (* pev_weak : f ↝[b1] f *)
  (Ha : r_evolution p a f f) :    (* aev_weak : f ↝[b1 # b2] f *)
  f <= w.
Proof.
  cut ((bot, f) <= compan); [intuition|].
  apply compat_below_compan. split; split.
  - constructor; intros R S _; unfold progress_mon; apply leq_bx.  (* bot ↝[b1] bot *)
  - exact Hp.
  - constructor; intros R S _; unfold progress_mon; apply leq_bx.  (* bot ↝[b2] f *)
  - exact Ha.
Qed.

(* Since the active obligation [aev_weak] is only the *conditional* b2-evolution,
   ordinary b2-compatibility ([f ° b2 <= b2 ° f]) is already enough for it -- the
   [R <= b1 R] premise is simply discarded.  So: a technique that is compatible
   with the ACTIVE behaviour and b1-evolves to itself is a sound active up-to. *)
Corollary compat_active_below_w (f : [X ⇒ X])
  (Hp : evolution p f f)          (* f b1-evolves to itself *)
  (Hc : f ° b2 <= b2 ° f) :       (* f is compatible with the active behaviour *)
  f <= w.
Proof.
  apply f_below_w; [ exact Hp | ].
  constructor. intros R S _ HRS.
  red.
  transitivity (f (b2 S)).
  - apply (Hbody f). exact HRS.
  - apply (Hc S).
Qed.

(* The combined behaviour is the meet, and the di-similarity of the pair is its
   greatest fixpoint: [R <= b1 R /\ R <= b2 R] iff [R <= (b1 ⊓ b2) R]. *)
Lemma di_similarity_meet_gfp : di_similarity p a == gfp (cap b1 b2).
Proof.
  apply antisym.
  - unfold di_similarity. apply sup_spec. intros R [H1 H2].
    apply leq_gfp. apply cap_spec. split; [ exact H1 | exact H2 ].
  - apply leq_xsup.
    pose proof (gfp_pfp (cap b1 b2)) as H. apply cap_spec in H.
    exact H.
Qed.

(* Lemma di_similarity_join_gfp : di_similarity p a == gfp (cup b1 b2).
Proof.
  apply antisym.
  - unfold di_similarity. apply sup_spec. intros R [H1 H2].
    apply leq_gfp. apply leq_xcup. now left. 
  - apply leq_xsup.
    pose proof (gfp_pfp (cup b1 b2)) as H.
    apply cup_spec.  
    Search cup. 
    
    apply leq_xcup in H.
    exact H.
Qed. *)

(* Both components are compatible w.r.t. the PASSIVE [b1] -- [pev_strong] for
   [u], [pev_weak] for [w] -- so both lie below the passive companion [t b1].
   This is the upper bound: [w] never rises above the passive companion. *)
Lemma u_below_t1 : u <= t b1.
Proof.
  apply leq_t. intro x.
  destruct (ucompan_p_compatible p a) as [Hu].
  apply (Hu (b1 x) x). unfold progress_mon. reflexivity.
Qed.

Lemma w_below_t1 : w <= t b1.
Proof.
  apply leq_t. intro x.
  destruct (wcompan_p_compatible p a) as [Hw].
  apply (Hw (b1 x) x). unfold progress_mon. reflexivity.
Qed.

Lemma u_below_w : u <= w.
Proof. apply (ucompan_below_wcompan p a). Qed.

(* Pinning down the bottom of [w]'s tower: [w bot] is *exactly* the combined
   bisimilarity, not an overshoot.

   - [<=]:  [bot] progresses (trivially, being least) to itself under both [p]
     and [a], and [w] preserves both progressions to itself ([wcompan_p_compatible]
     gives [w bot ↣ₚ w bot], [wcompan_a_compatible] gives [w bot ↣ₐ w bot]).
     So [w bot] self-progresses in both, hence sits in [di_similarity].
   - [>=]:  the constant [di_similarity] is below [w] ([disim_const_below_wcompan]),
     so [di_similarity <= w bot]. *)
Lemma w_bot_eq_di_similarity : w bot == di_similarity p a.
Proof.
  apply antisym.
  - apply leq_xsup. split.
    + destruct (wcompan_p_compatible p a) as [Hw].
      apply (Hw bot bot). unfold progress_mon. apply leq_bx.
    + destruct (wcompan_a_compatible p a) as [Hw'].
      apply (Hw' bot bot); unfold progress_mon; apply leq_bx.
  - apply (disim_const_below_wcompan p a bot).
Qed.

(* Hence [w]'s tower bottoms out at the combined bisimilarity.
  Thus [w] is a sound enhancement; its fixpoint from [bot] is the gfp, 
  just like [t]. *)
Corollary w_bot_gfp : w bot == gfp (cap b1 b2).
Proof. rewrite w_bot_eq_di_similarity. apply di_similarity_meet_gfp. Qed.
Lemma w_top : w top == top. 
Proof. apply antisym. 
    - apply leq_xt. 
    - cbn. eapply eleq_xsup. 
      unshelve (instantiate (1:=p_id)). 
      + apply id_compatible; typeclasses eauto. 
      + reflexivity. 
Qed. 
Print tower.C. 

(* we want the w-tower *)
(* so that by w-tower-induction we can prove conditional soundness
   of techniques. *)

   (* idea: fix (s) of (s, f) to be b-realted. then we can 
      specify the restrictions on f from that using the rules w.r.t. an existing b, 
      and then have a hole for soundness. *)

(* an essential precondition result of this approach is that conditional soundness
w.r.t. b - i.e., f being conditionally sound because (b, f) is sound - 
is sufficient criteria for identifying _any_ conditionally sound up-to funciton.  *)

(* Why the collapse argument from [Section pairs] breaks here, and what stays
   open:

   - [t b] for [b = b1 ⊓ b2] is compatible w.r.t. [b1 ⊓ b2], i.e.
     [t b ((b1 ⊓ b2) R) <= (b1 ⊓ b2)(t b R)].  But [pev_strong]/[pev_weak]
     demand compatibility w.r.t. [b1] ALONE: [R <= b1 S -> t b R <= b1 (t b S)].
     Knowing only [R <= b1 S] (not [R <= b2 S]) we cannot reach [R <= b S], so
     [t_step] no longer applies and [(t b, t b)] is NOT provably compatible.
     Hence the easy [t b <= w] route is gone.

   - The active asymmetry is now real: [u] must satisfy the *unconditional*
     [aev_strong]  [R <= b2 S -> u R <= b2 (w S)], while [w]'s only active
     obligation is the *conditional* [aev_weak]
     [R <= b1 R -> R <= b2 S -> w R <= b2 (w S)].  The extra premise [R <= b1 R]
     is what lets [w] exceed [t b].

   Conjecture (the [w > t b] phenomenon):  [t b <= w] with [t b < w] possible,
   so the combined companion is sandwiched:  [t (b1 ⊓ b2) <= w <= t b1]. *)
Lemma t_comb_below_w : t (cap b1 b2) <= w.
Proof.
Abort. 



Require Import tower rel. 
(* Notation Chain := (Chain (cap b1 b2)). *)
Notation "` x" := (elem x) (at level 2).

Notation b' := (cap b1 b2).

(* w preserves members of the chain of b1 *)
Proposition w_in_tower_b1 : forall x : Chain b1, w `x == `x. 
Proof.
  intros. apply antisym. 
  - rewrite w_below_t1. apply chain.t_chain. 
  - rewrite <- id_below_wcompan; try typeclasses eauto. 
  reflexivity. 
Qed. 
  
(* what about b'? *)

Proposition w_in_tower_b' : forall x : Chain b', `x <= w `x. 
Proof.
  intros. rewrite <- id_below_wcompan; try typeclasses eauto. 
  reflexivity. 
Qed. 




(* Does w preserve the COMBINED tower (the reverse of w_in_tower_b')?
   Attempt by tower induction; watch where it stalls. *)
Proposition w_in_tower_b'_rev : forall x : Chain b', w `x <= `x.
Proof.
  apply (tower (P := fun y => w y <= y)).
  - apply inf_closed_leq.
  - intros x IH. apply cap_spec. split.
    + (* w (b' `x) <= b1 `x : passive half, unconditional (pev_weak) *)
      destruct (wcompan_p_compatible p a) as [Hw].
      transitivity (b1 (w `x)).
      * apply (Hw (b' `x) `x). apply cap_l.
      * now apply b1.
    + (* w (b' `x) <= b2 `x : active half (aev_weak) *)
      destruct (wcompan_a_compatible p a) as [Hw'].
      transitivity (b2 (w `x)).
      * apply (Hw' (b' `x) `x).
        -- (* PREMISE: b' `x <= b1 (b' `x)  -- b' `x must be a b1-post-fixpoint *)
           admit.
        -- apply cap_r.
      * now apply b2.
Abort.
(* Conclusion: the reverse reduces to [b' `x <= b1 (b' `x)] (a b1-post-fixpoint
   condition on the b'-image), which the diacritical laws do NOT supply and which
   fails at large chain elements.  So [w] is NOT absorbed by the combined chain,
   and tower induction over [Chain b'] cannot host the active up-to.  It IS hosted
   by the passive chain [Chain b1] ([w_in_tower_b1]). *)

(* The usable diacritical coinduction principle: to land in the combined gfp,
   progress passively via [u] and actively via [w].  This is the "swap" target
   (Pous' [soundness], with [di_similarity = gfp b'] plugged in). *)
Corollary di_coinduction (R : X) : R ↣ₚ u R -> R ↣ₐ w R -> R <= gfp b'.
Proof.
  intros H1 H2. rewrite <- chain.gfp_tower, <- di_similarity_meet_gfp.
  now apply (soundness p a).
Qed.

(* ------------------------------------------------------------------------- *)
(** ** Ergonomic swap layer: up-to-enhanced diacritical coinduction.

    [di_coinduction] asks you to progress passively into [u R] and actively
    into [w R].  Using [u]/[w] directly is awkward -- the whole point of an
    up-to technique is to progress into a *smaller*, easier target.  These
    wrappers let you discharge each obligation with ANY sound technique:
      - passive side: any [f <= u]  (e.g. [id], or any passive enhancement);
      - active side:  any [g <= w].
    Progress monotonicity in the target ([progress_monotone_r]) closes the gap,
    so the two remaining obligations are the *enhanced* progressions
    [R ↣ₚ f R] and [R ↣ₐ g R]. *)
Corollary di_coinduction_upto (R : X) (f g : [X ⇒ X])
  (Hf : f <= u) (Hg : g <= w) :
  R ↣ₚ f R -> R ↣ₐ g R -> R <= gfp b'.
Proof.
  intros H1 H2. apply di_coinduction.
  - eapply progress_monotone_r; [ apply (Hf R) | exact H1 ].
  - eapply progress_monotone_r; [ apply (Hg R) | exact H2 ].
Qed.

(* The headline use of the swap: the ACTIVE technique [g] need only be
   active-compatible ([g ° b2 <= b2 ° g]) and passively self-evolving
   ([evolution p g g]) -- [compat_active_below_w] then certifies [g <= w] with
   the strong partner taken to be [bot].  Such a [g] is generally UNSOUND as an
   ordinary (passive) up-to technique, but is sound in active positions; the
   swap is exactly what makes it usable.  This is the concrete realisation of
   "swap to the diacritical companion when you need active-only power". *)
Corollary di_coinduction_active (R : X) (f g : [X ⇒ X])
  (Hf : f <= u)
  (Hgp : evolution p g g)          (* g b1-evolves to itself *)
  (Hgc : g ° b2 <= b2 ° g) :       (* g is compatible with the active behaviour *)
  R ↣ₚ f R -> R ↣ₐ g R -> R <= gfp b'.
Proof.
  intros H1 H2.
  apply (di_coinduction_upto R f g).
  - exact Hf.
  - apply compat_active_below_w; assumption.
  - exact H1.
  - exact H2.
Qed.

(* Ergonomic front-ends.  [di_swap with f , g] reduces a [_ <= gfp b'] goal to
   four obligations: [f <= u], [g <= w], and the two enhanced progressions.
   [di_swap_active with f , g] instead asks for [g]'s two active-soundness laws,
   so an active-only technique can be dropped in without proving [g <= w] by
   hand. *)
Tactic Notation "di_swap" "with" constr(f) "," constr(g) :=
  apply (di_coinduction_upto _ f g).
Tactic Notation "di_swap_active" "with" constr(f) "," constr(g) :=
  apply (di_coinduction_active _ f g).

(* Sanity check that the swap layer actually fires and leaves the expected
   obligations.  Taking both techniques to be the identity recovers plain
   coinduction into [gfp b'] with no enhancement, via [id <= u] / [id <= w]
   ([id_below_ucompan] / [id_below_wcompan]). *)
Example di_swap_id (R : X) :
  R ↣ₚ id R -> R ↣ₐ id R -> R <= gfp b'.
Proof.
  intros H1 H2.
  di_swap with (id : [X ⇒ X]) , (id : [X ⇒ X]).
  - apply id_below_ucompan; typeclasses eauto.   (* id <= u *)
  - apply id_below_wcompan; typeclasses eauto.   (* id <= w *)
  - exact H1.                 (* R ↣ₚ id R *)
  - exact H2.                 (* R ↣ₐ id R *)
Qed.

(* is w actually preserving tower membership? *)


(* etransitivity. 
    apply (rule_coind). 
    unshelve (instantiate (1:=_)).
    exact `x. 
    unshelve (instantiate (1:=_)).
    exact (b'). unfold bt. 
    cbn. Search cap. 
    Search ( _ <= t _).
  2: eapply chain.t_chain.
  transitivity (b1 (t b1 (cup `x (t b1 `x)))).
  shelve. 

  apply cap_spec. split. 
  apply b1.  

  - apply id_below_wcompan; typeclasses eauto. 
Abort.  *)

(* ========================================================================= *)
(** ** The SECOND-ORDER tower: the diacritical companion IS a gfp.

    [diacritical_redesign.v] shows no FIRST-order tower on the base lattice [X]
    can host the active power: the active guard [R <= b1 R] is a post-fixpoint
    (below-gfp) condition, orthogonal to a base-lattice pre-fixpoint chain.

    But the companion pair [(u,w)] is *by definition* a [di_similarity] on the
    PAIR lattice [L_lift X] ([compan_is_disim]), and a di_similarity of progress
    relations IS a gfp: reading each evolution progression back as a monotone
    operator ([mon_of_progress]) and meeting them yields a monotone second-order
    operator [B_di] on [L_lift X] with [compan == gfp B_di].  The guard is now
    harmless -- baked into [B_di] as a fixed side-condition on [R], not a demand
    at chain elements -- so monotonicity survives.  Hence the diacritical
    companion HAS a tower: a second-order one, exactly as Pous' [B]/[T] give the
    ordinary companion its tower ([companion.companion_gfp]). *)

Notation Pev := (p_evolution p).
Notation Aev := (a_evolution p a).

Definition B_di : mon (L_lift X) :=
  cap (mon_of_progress Pev) (mon_of_progress Aev).

(* [(u,w)] is the greatest post-fixpoint of [B_di]: the companion is a gfp. *)
Lemma compan_gfp : compan == tower.gfp B_di.
Proof.
  apply antisym.
  - unfold diacritical_companion.compan. apply sup_spec. intros f [H1 H2].
    apply tower.leq_gfp. apply cap_spec. split.
    + apply (proj1 (progress_mon_of Pev f f)). exact H1.
    + apply (proj1 (progress_mon_of Aev f f)). exact H2.
  - unfold diacritical_companion.compan. apply leq_xsup.
    pose proof (tower.gfp_pfp B_di) as H. apply cap_spec in H. destruct H as [HP HA].
    split.
    + apply (proj2 (progress_mon_of Pev _ _)). exact HP.
    + apply (proj2 (progress_mon_of Aev _ _)). exact HA.
Qed.

(* A pair is a post-fixpoint of [B_di] exactly when it is a compatible pair --
   this is the diacritical analogue of [companion.B_spec], and it is what makes
   [B_di] the right second-order operator. *)
Lemma B_di_spec (f : L_lift X) : f <= B_di f <-> compatible p a f.
Proof.
  split.
  - intro H. apply cap_spec in H. destruct H as [HP HA]. split.
    + apply (proj2 (progress_mon_of Pev f f)). exact HP.
    + apply (proj2 (progress_mon_of Aev f f)). exact HA.
  - intros [HP HA]. apply cap_spec. split.
    + apply (proj1 (progress_mon_of Pev f f)). exact HP.
    + apply (proj1 (progress_mon_of Aev f f)). exact HA.
Qed.

(* Raw second-order tower induction: any inf-closed property preserved by one
   [B_di]-step holds at every element of the diacritical chain. *)
Corollary di_chain_ind (Q : L_lift X -> Prop) :
  inf_closed Q ->
  (forall x : Chain B_di, Q (elem x) -> Q (B_di (elem x))) ->
  forall x : Chain B_di, Q (elem x).
Proof. apply tower.tower. Qed.

(* ...and, transported to the bottom of the chain, it holds of the companion
   pair [(u,w)] itself.  THIS is "tower induction based on the diacritical
   companion": pick an inf-closed invariant on pairs, show one [B_di]-step
   preserves it, and conclude it of [(u,w)]. *)
Lemma di_tower (Q : L_lift X -> Prop) :
  Proper (weq ==> Basics.impl) Q ->
  inf_closed Q ->
  (forall x : Chain B_di, Q (elem x) -> Q (B_di (elem x))) ->
  Q compan.
Proof.
  intros HQ Hinf Hstep.
  eapply HQ; [ symmetry; apply compan_gfp | ].
  apply tower.gfp_prop.
  exact (tower.tower (b := B_di) Hinf Hstep).
Qed.

(* Demonstration: reflexivity of the companion ([p_id <= (u,w)]) by SECOND-ORDER
   tower induction.  [id_compatible] gives the one-step post-fixpoint
   [p_id <= B_di p_id]; monotonicity of [B_di] carries it up every chain step;
   [di_tower] lands it at the companion.  (Cf. [id_below_compan], which proves
   the same thing directly by coinduction -- here it falls out of the tower.) *)
Example id_below_compan_via_tower : p_id <= compan.
Proof.
  apply di_tower.
  - intros u v Huv H. now rewrite <- Huv.
  - intros T HT. apply inf_spec. intros x Tx. now apply HT.
  - intros x IH. transitivity (B_di p_id).
    + apply B_di_spec. apply id_compatible; typeclasses eauto.
    + apply B_di. exact IH.
Qed.

End diacritical_two.

(* ========================================================================= *)
(** ** A genuinely ACTIVE-ONLY up-to technique, via [(bot, f) <= (u,w)].

    [f_below_w] takes the strong partner to [bot], leaving two f-laws: [f] is
    [b1]-compatible ([Hp]) and CONDITIONALLY [b2]-compatible ([Ha], available
    only under [R <= b1 R]).  For an active-ONLY technique the premise must be
    load-bearing -- otherwise [compat_active_below_w] applies and the technique
    is sound everywhere ([<= t b']).

    The prototypical such technique is [f := b1] itself: "after an active step
    you may take one passive step."  Its [b1]-compatibility is automatic
    (monotonicity).  Its ACTIVE law is exactly the coupling below: matching an
    active step through one passive step is sound *precisely when* the candidate
    is already a passive simulation ([R <= b1 R]).  This [couple] law is the
    algebraic essence of a weak-transition system -- and it is exactly what
    FAILS for the decoupled streams in [Section example] (there [b1 R] relates
    differently-labelled [β]'s, which [b2] rejects), which is why the passive
    step [b1] is not a sound active enhancement there. *)
Section active_only.
Context {X : Type} {CL : CompleteLattice X}.
Variable b1 b2 : mon X.

Notation p := (progress_mon b1).
Notation a := (progress_mon b2).
#[local] Instance QP1 : Progress (progress_mon b1) := progress_mono b1.
#[local] Instance QP2 : Progress (progress_mon b2) := progress_mono b2.
Notation w := (snd (diacritical_companion.compan p a)).

(* The coupling law.  Note the premise [R <= b1 R]: WITHOUT it this is false in
   general (that is what makes [b1] active-only rather than compatible). *)
Hypothesis couple :
  forall R S : X, R <= b1 R -> R <= b2 S -> b1 R <= b2 (b1 S).

Theorem b1_active_only : b1 <= w.
Proof.
  apply (f_below_w b1 b2 b1).
  - (* Hp : evolution p b1 b1 -- b1 is b1-compatible, by monotonicity *)
    constructor. intros R S HRS. apply b1. exact HRS.
  - (* Ha : r_evolution p a b1 b1 -- the CONDITIONAL active law, = [couple] *)
    constructor. intros R S Hpre HRS. apply couple; assumption.
Qed.

End active_only.


Section example.


CoInductive stream :=
 | τ (s : stream)
 | β (n : nat) (k:stream).

Notation "'τ' s"   := (τ s) (at level 35, right associativity).
Notation "'(β' n ')' k" := (β n k) (at level 35, n at level 0, k at level 35).

Variant b_passive (bisim : stream -> stream -> Prop) : stream -> stream -> Prop := 
| bisim_faux_beta n m s1 s2 : b_passive bisim ((β n) s1) ((β m) s2) 
| bisim_tau s1 s2 : bisim s1 s2 -> b_passive bisim (τ s1) (τ s2). 
Variant b_active (bisim : stream -> stream -> Prop) : stream -> stream -> Prop := 
| bisim_faux_tau s1 s2 : b_active bisim (τ s1) (τ s2) 
| bisim_beta n s1 s2 : bisim s1 s2 -> b_active bisim ((β n) s1) ((β n) s2). 

Program Definition b1 : mon (stream -> stream -> Prop) := {| body := b_passive |}.
Next Obligation. 
monauto. 
Qed. 

Program Definition b2 : mon (stream -> stream -> Prop) := {| body := b_active |}.
Next Obligation. 
monauto. 
Qed.

Definition bisim_passive := gfp b1. 
Definition bisim_active := gfp b2. 

Notation p := (progress_mon b1).
Notation a := (progress_mon b2).

Instance Pp : Progress p
         := progress_mono b1. 

Instance Pa : Progress a 
         := progress_mono b2. 

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).  
Notation w := (snd compan).  

Notation b' := (cap b1 b2).

(* 
CL mon X 
b' := b1 ∩ b2 
        
                                
        t b1 

        w bot = gfp 
        
        t b' (x) in the tower 

        
        ⊤
        b ⊤

        hole 
        ... 

        hole 

        gfp b 

R ↣ R := R bisimulation 



*)


Lemma disim_gfp : di_similarity p a == gfp b'. 
Proof.   
  apply antisym. 
  - unfold di_similarity. apply sup_spec. intros i [H H0]. 
  rewrite chain.gfp_tower. 
  repeat red. 
  coinduction c cih. intros. 
  apply H in H1 as H2.  
  apply H0 in H1 as H3.
  inv H2. 
  + split. 
    * constructor. 
    * inv H3. 
      constructor.
      apply cih. apply H4. 
  + split. 
    * constructor. 
      apply cih. inv H3.
    * constructor.  
  - apply leq_xsup. split; repeat red; intros. 
    all: apply (gfp_pfp b') in H.
    all: inv H. 
Qed. 

(* Proposition tb_leq_w : t b' <= w.
Proof. 
  repeat red.  
  intros sim s1 s2 Ht.
  exists (t b1, t b2). 
  2 : auto. 
  (* 4 cases *)
  split. 
  - constructor.
   (* 1: t b1 b1-evolves to t b1 *)
  + cbn. constructor. intros. 
    repeat red. intros. 
    repeat red in H.
    cbn in H0.  *)
        
    
    
(* ------------------------------------------------------------------------- *)
(* A concrete up-to technique certified for the ACTIVE companion [w] by the
   diacritical machinery.  [compat_active_below_w] (the [s := bot] reduction)
   discharges [rG <= w] from two [rG]-laws: [rG] is [b1]-compatible and
   [b2]-compatible.  Here we use up-to-reflexivity [rG R = R ∪ Δ]. *)
Program Definition rG : mon (stream -> stream -> Prop) :=
  {| body R := cup R (fun x y => x = y) |}.
Next Obligation. intros R S H x y [HR|He]. left; now apply H. now right. Qed.

Lemma rG_below_w : rG <= w.
Proof.
  apply (compat_active_below_w b1 b2 rG).
  - (* evolution p rG rG : rG is b1-compatible *)
    constructor. intros R S HRS. apply cup_spec. split.
    + transitivity (b1 S); [ exact HRS | apply b1; apply cup_l ].
    + intros x y Heq; subst y. destruct x as [s | n s].
      * apply bisim_tau. right; reflexivity.
      * apply bisim_faux_beta.
  - (* rG ° b2 <= b2 ° rG : rG is b2-compatible *)
    intro R. apply cup_spec. split.
    + apply b2; apply cup_l.
    + intros x y Heq; subst y. destruct x as [s | n s].
      * apply bisim_faux_tau.
      * apply bisim_beta. right; reflexivity.
Qed.

(* Note: [rG] is *also* passively sound (the proof establishes full
   [b1]- and [b2]-compatibility), so it lies below [t b'] too.  A technique that
   is active-ONLY ([<= w] but [</= t b']) needs the passive and active
   behaviours to be COUPLED -- so that the active law's premise [R <= b1 R]
   feeds an active obligation.  These streams are decoupled ([b1] constrains
   [τ]-continuations, [b2] constrains [β]-labels), so that phenomenon does not
   arise here; certifying such a technique is where the second-order tower
   ([di_tower] / up-to-companion via [B_di]) does the real work. *)

(* And concretely: the coupling law [couple] from [Section active_only] FAILS
   for these decoupled streams, so [b1] is genuinely not a sound active
   enhancement here.  Witness [R = S = bot]: [b1 bot] relates the
   differently-labelled [β 0 w0] and [β 1 w0] (passive [faux_beta]), but
   [b2 (b1 bot)] cannot (active [β] demands equal labels). *)
CoFixpoint w0 : stream := τ w0.

Remark couple_fails_for_streams :
  ~ (forall R S : stream -> stream -> Prop,
        R <= b1 R -> R <= b2 S -> b1 R <= b2 (b1 S)).
Proof.
  intro H. specialize (H bot bot (leq_bx _) (leq_bx _)).
  assert (Hpair : b1 bot ((β 0) w0) ((β 1) w0)) by apply bisim_faux_beta.
  apply H in Hpair. inversion Hpair.
Qed.

(* Eval stop_here in True.  *)
End example.
(* ========================================================================= *)
(** ** Higher-order: running the companion on the lattice of RELATIONS.

   The companion theory above is parametric in the carrier lattice [X].  Taking
   [X := A -> A -> Prop] with its *canonical* pointwise lattice
   ([CompleteLattice_dfun] over [CompleteLattice_Prop]) turns the abstract
   theory into concrete coinduction-up-to:

     - lattice elements        = relations on [A];
     - [<=]                     = relation inclusion;
     - [cap]/[cup]/[top]/[bot]  = intersection / union / full / empty relation;
     - a monotone [b : mon Rel] = a behaviour (an "observation" functor);
     - [gfp b]                  = the coinductively defined relation;
     - monotone [f : mon Rel]   = an up-to technique, and [t b] the greatest
                                  sound one; the diacritical [(u, w)] is its
                                  passive/active split.

   None of the *theorems* change -- they apply at [X := Rel] verbatim -- but
   this is the level where they have computational meaning. *)

Section relation_lattice.
Context {A : Type}.
Notation Rel := (A -> A -> Prop).

(* With the canonical instance the lattice operations are *definitionally* the
   relational ones, so the earlier [top] question is now provable (there is no
   abstract [c] to hide the order): [top] really is the full relation. *)
Lemma rel_top   : (top : Rel) = fun _ _ => True.  Proof. reflexivity. Qed.
Lemma rel_bot   : (bot : Rel) = fun _ _ => False. Proof. reflexivity. Qed.
Lemma rel_cap (R S : Rel) : cap R S = fun x y => R x y /\ S x y. Proof. reflexivity. Qed.
Lemma rel_cup (R S : Rel) : cup R S = fun x y => R x y \/ S x y. Proof. reflexivity. Qed.
Lemma rel_leq (R S : Rel) : (R <= S) <-> (forall x y, R x y -> S x y).
Proof. split; intro H; exact H. Qed.

(* The fixed version of the line-196 goal, over the canonical [dfun] lattice. *)
Lemma top_rel_refl (x : A) : (top : Rel) x x == True.
Proof. cbn. tauto. Qed.

End relation_lattice.

(* ------------------------------------------------------------------------- *)
(** A concrete behaviour: the simulation functor of a transition relation
    [step].  This grounds the abstract machinery -- [gfp sim] is similarity, and
    a coinductive proof about it is just a post-fixpoint witness fed to
    [leq_gfp]. *)

Section simulation.
Context {A : Type} (step : A -> A -> Prop).
Notation Rel := (A -> A -> Prop).

Program Definition sim : mon Rel :=
  {| body R := fun x y => forall x', step x x' -> exists2 y', step y y' & R x' y' |}.
Next Obligation.
  intros R S HRS x y H x' Hx'.
  destruct (H x' Hx') as [y' Hstep HR]. 
  exists y'; [ exact Hstep | exact (HRS x' y' HR) ].
Qed.

(* One-step unfolding of similarity, straight from [gfp_fp]. *)
Lemma similarity_unfold x y :
  gfp sim x y <-> forall x', step x x' -> exists2 y', step y y' & gfp sim x' y'.
Proof. exact (gfp_fp sim x y). Qed.

(* Reflexivity by coinduction: equality is a post-fixpoint of [sim]. *)
Lemma eq_below_similarity : (fun a b : A => a = b) <= gfp sim.
Proof.
  apply leq_gfp. intros a b Hab a' Ha'.
  exists a'; [ rewrite <- Hab; exact Ha' | reflexivity ].
Qed.

Lemma similarity_refl x : gfp sim x x.
Proof. exact (eq_below_similarity x x eq_refl). Qed.

(* Transitivity by coinduction: relational composition is a post-fixpoint.
   Packaged as a technique this is exactly "up-to-transitivity", which lives
   below the companion [t sim]. *)
Lemma comp_below_similarity :
  (fun x z => exists y, gfp sim x y /\ gfp sim y z) <= gfp sim.
Proof.
  apply leq_gfp. intros x z [y [Hxy Hyz]] x' Hx'.
  pose proof (proj1 (similarity_unfold x y) Hxy x' Hx') as [y' Hyy' Hx'y'].
  pose proof (proj1 (similarity_unfold y z) Hyz y' Hyy') as [z' Hzz' Hy'z'].
  exists z'; [ exact Hzz' | exists y'; split; assumption ].
Qed.

Lemma similarity_trans x y z : gfp sim x y -> gfp sim y z -> gfp sim x z.
Proof.
  intros Hxy Hyz. apply (comp_below_similarity x z). exists y; split; assumption.
Qed.

(* The abstract diacritical results transfer for free.  With [sim] used as both
   the passive and active progression, the passive companion [u] is just the
   ordinary companion [t sim] -- this is [u_t] instantiated at [Rel]. *)
#[local] Instance Psim : Progress (progress_mon sim) := progress_mono sim.

Example similarity_passive_companion :
  fst (compan (progress_mon sim) (progress_mon sim)) == t sim.
Proof. exact (u_t sim). Qed.

  (* w's image is in the tower *)



End simulation.