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

(* [R ↣ₚ R ∧ R ↣ₐ R] is just [R <= b R], ergo the di-similarity of the pair is the
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





Lemma t_step R S : R <= b S -> t R <= b (t S).
Proof.
  intro H. transitivity (t (b S)).
  - apply (Hbody t). exact H.
  - apply (compat_t b S).
Qed.


Lemma u_leq_t : u <= t.
Proof.
  apply leq_t. intro x.
  destruct (ucompan_p_compatible p a) as [Hu].
  apply (Hu (b x) x). unfold progress_mon. reflexivity.
Qed.

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


Lemma w_leq_t : w <= t.
Proof.
  apply leq_t. intro x.
  destruct (wcompan_p_compatible p a) as [Hw].
  apply (Hw (b x) x). unfold progress_mon. reflexivity.
Qed.

Proposition w_t : w == t.
Proof. apply antisym; [ apply w_leq_t | apply t_leq_w ]. Qed.

End pairs.


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


Lemma di_similarity_meet_gfp : di_similarity p a == gfp (cap b1 b2).
Proof.
  apply antisym.
  - unfold di_similarity. apply sup_spec. intros R [H1 H2].
    apply leq_gfp. apply cap_spec. split; [ exact H1 | exact H2 ].
  - apply leq_xsup.
    pose proof (gfp_pfp (cap b1 b2)) as H. apply cap_spec in H.
    exact H.
Qed.


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
   Attempt by tower induction; currently fails *)
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

Corollary di_coinduction (R : X) : R ↣ₚ u R -> R ↣ₐ w R -> R <= gfp b'.
Proof.
  intros H1 H2. rewrite <- chain.gfp_tower, <- di_similarity_meet_gfp.
  now apply (soundness p a).
Qed.


Corollary di_coinduction_upto (R : X) (f g : [X ⇒ X])
  (Hf : f <= u) (Hg : g <= w) :
  R ↣ₚ f R -> R ↣ₐ g R -> R <= gfp b'.
Proof.
  intros H1 H2. apply di_coinduction.
  - eapply progress_monotone_r; [ apply (Hf R) | exact H1 ].
  - eapply progress_monotone_r; [ apply (Hg R) | exact H2 ].
Qed.

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

Tactic Notation "di_swap" "with" constr(f) "," constr(g) :=
  apply (di_coinduction_upto _ f g).
Tactic Notation "di_swap_active" "with" constr(f) "," constr(g) :=
  apply (di_coinduction_active _ f g).


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


Corollary di_tower_gfp (Q : L_lift X -> Prop) :
  inf_closed Q ->
  (forall x : Chain B_di, Q (elem x) -> Q (B_di (elem x))) ->
  Q (tower.gfp B_di).
Proof.
  intros Hinf Hstep. apply tower.gfp_prop.
  exact (tower.tower (b := B_di) Hinf Hstep).
Qed.

(* the companion is below every chain element, in particular below the gfp *)
Lemma gfp_B_di_below_compan : tower.gfp B_di <= compan.
Proof. pose proof compan_gfp as E. apply weq_spec in E. apply E. Qed.



Lemma inf_closed_leq_snd (f : [X ⇒ X]) : inf_closed (fun q : L_lift X => f <= snd q).
Proof. intros T HT. apply inf_spec. intros q Tq. now apply HT. Qed.

Lemma inf_closed_leq_fst (f : [X ⇒ X]) : inf_closed (fun q : L_lift X => f <= fst q).
Proof. intros T HT. apply inf_spec. intros q Tq. now apply HT. Qed.


Proposition leq_w_chain_ind (f : [X ⇒ X]) :
  (forall x : Chain B_di, f <= snd (elem x) -> f <= snd (B_di (elem x))) ->
  forall x : Chain B_di, f <= snd (elem x).
Proof. exact (tower.tower (b := B_di) (inf_closed_leq_snd f)). Qed.

Proposition leq_u_chain_ind (f : [X ⇒ X]) :
  (forall x : Chain B_di, f <= fst (elem x) -> f <= fst (B_di (elem x))) ->
  forall x : Chain B_di, f <= fst (elem x).
Proof. exact (tower.tower (b := B_di) (inf_closed_leq_fst f)). Qed.


Theorem leq_w_chain (f : [X ⇒ X]) :
  f <= w <-> forall x : Chain B_di, f <= snd (elem x).
Proof.
  pose proof compan_gfp as E. apply weq_spec in E. destruct E as [E1 E2].
  split.
  - intros H x. rewrite H. transitivity (snd (tower.gfp B_di)).
    + exact (proj2 E1).
    + exact (proj2 (gfp_chain x)).
  - intro H. transitivity (snd (tower.gfp B_di)).
    + exact (H (chain_gfp B_di)).
    + exact (proj2 E2).
Qed.

Theorem leq_u_chain (f : [X ⇒ X]) :
  f <= u <-> forall x : Chain B_di, f <= fst (elem x).
Proof.
  pose proof compan_gfp as E. apply weq_spec in E. destruct E as [E1 E2].
  split.
  - intros H x. rewrite H. transitivity (fst (tower.gfp B_di)).
    + exact (proj1 E1).
    + exact (proj1 (gfp_chain x)).
  - intro H. transitivity (fst (tower.gfp B_di)).
    + exact (H (chain_gfp B_di)).
    + exact (proj1 E2).
Qed.


Corollary w_chain (x : Chain B_di) : w <= snd (elem x).
Proof. now apply leq_w_chain. Qed.
Corollary u_chain (x : Chain B_di) : u <= fst (elem x).
Proof. now apply leq_u_chain. Qed.


Corollary id_below_snd_chain (x : Chain B_di) : id <= snd (elem x).
Proof.
  transitivity (snd (diacritical_companion.compan p a)).
  - apply id_below_wcompan; typeclasses eauto.
  - apply w_chain.
Qed.

Corollary disim_below_snd_chain (x : Chain B_di) :
  const (di_similarity p a) <= snd (elem x).
Proof.
  transitivity (snd (diacritical_companion.compan p a)).
  - apply disim_const_below_wcompan; typeclasses eauto.
  - apply w_chain.
Qed.

Corollary id_below_fst_chain (x : Chain B_di) : id <= fst (elem x).
Proof.
  transitivity (fst (diacritical_companion.compan p a)).
  - apply id_below_ucompan; typeclasses eauto.
  - apply u_chain.
Qed.


Lemma leq_snd_B_di (f : [X ⇒ X]) (g : L_lift X)
  (HP : forall R S : X, R <= b1 S -> f R <= b1 (snd g S))
  (HA : forall R S : X, R <= b1 R -> R <= b2 S -> f R <= b2 (snd g S)) :
  f <= snd (B_di g).
Proof.
  assert (H1 : ((bot, f) : L_lift X) <= mon_of_progress Pev g).
  { apply leq_xsup. split.
    - constructor; intros R S _; unfold progress_mon; apply leq_bx.
    - constructor; intros R S HRS; exact (HP R S HRS). }
  assert (H2 : ((bot, f) : L_lift X) <= mon_of_progress Aev g).
  { apply leq_xsup. split.
    - constructor; intros R S _; unfold progress_mon; apply leq_bx.
    - constructor; intros R S Hpre HRS; exact (HA R S Hpre HRS). }
  apply cap_spec. split; [ exact (proj2 H1) | exact (proj2 H2) ].
Qed.

Lemma f_below_w_tower (f : [X ⇒ X])
  (Hstep : forall x : Chain B_di,
      f <= snd (elem x) ->
      (forall R S : X, R <= b1 S -> f R <= b1 (snd (elem x) S))
      /\ (forall R S : X, R <= b1 R -> R <= b2 S -> f R <= b2 (snd (elem x) S))) :
  f <= w.
Proof.
  apply leq_w_chain. apply leq_w_chain_ind.
  intros x IH. destruct (Hstep x IH) as [HP HA].
  exact (leq_snd_B_di f (elem x) HP HA).
Qed.

Corollary f_below_w_cup (f : [X ⇒ X])
  (Hp : forall R S : X, R <= b1 S -> f R <= b1 (cup (f S) S))
  (Ha : forall R S : X, R <= b1 R -> R <= b2 S -> f R <= b2 (cup (f S) S)) :
  f <= w.
Proof.
  apply f_below_w_tower. intros x IH. split.
  - intros R S H. transitivity (b1 (cup (f S) S)).
    + apply Hp, H.
    + apply b1. apply cup_spec. split.
      * apply (IH S).
      * apply (id_below_snd_chain x S).
  - intros R S Hpre H. transitivity (b2 (cup (f S) S)).
    + apply Ha; assumption.
    + apply b2. apply cup_spec. split.
      * apply (IH S).
      * apply (id_below_snd_chain x S).
Qed.


Corollary f_below_w_b (f : [X ⇒ X])
  (Hp : forall R S : X, R <= b1 S -> f R <= b1 (f S))
  (Ha : forall R S : X, R <= b1 R -> R <= b2 S -> f R <= b2 (f S)) :
  f <= w.
Proof.
  apply f_below_w_tower. intros x IH. split.
  - intros R S HRS. transitivity (b1 (f S)); [ apply Hp, HRS | apply b1, IH ].
  - intros R S Hpre HRS. transitivity (b2 (f S)); [ apply Ha; assumption | apply b2, IH ].
Qed.


Example id_below_compan_via_tower : p_id <= compan.
Proof.
  transitivity (tower.gfp B_di); [ | exact gfp_B_di_below_compan ].
  apply (di_tower_gfp (fun q => p_id <= q)).
  - intros T HT. apply inf_spec. intros q Tq. now apply HT.
  - intros x IH. transitivity (B_di p_id).
    + apply B_di_spec. apply id_compatible; typeclasses eauto.
    + apply B_di. exact IH.
Qed.


Definition b_uw : mon X := cap (b1 ° u) (b2 ° w).

Lemma b_below_b_uw : cap b1 b2 <= b_uw.
Proof.
  intro S. apply cap_spec. split.
  - transitivity (b1 S); [ apply cap_l | ].
    apply b1. apply id_below_ucompan; typeclasses eauto.
  - transitivity (b2 S); [ apply cap_r | ].
    apply b2. apply id_below_wcompan; typeclasses eauto.
Qed.

(* guarding does not change the greatest fixpoint: [soundness] is exactly the
   statement that a [b_uw]-post-fixpoint is a bisimulation *)
Theorem gfp_b_uw : tower.gfp b_uw == tower.gfp (cap b1 b2).
Proof.
  apply antisym.
  - (* the substance: unfold once, then apply diacritical soundness *)
    pose proof (tower.gfp_pfp b_uw) as H. apply cap_spec in H. destruct H as [Hp Ha].
    transitivity (di_similarity p a).
    + apply (diacritical_companion.soundness p a); assumption.
    + rewrite di_similarity_meet_gfp. rewrite chain.gfp_tower. reflexivity.
  - apply gfp_leq. exact b_below_b_uw.
Qed.

Corollary active_upto (f : [X ⇒ X]) (Hf : f <= w) (x : Chain b_uw) :
  f (elem x) <= w (elem x).
Proof. apply Hf. Qed.

Corollary passive_upto (f : [X ⇒ X]) (Hf : f <= u) (x : Chain b_uw) :
  f (elem x) <= u (elem x).
Proof. apply Hf. Qed.

End diacritical_two.


Tactic Notation "di_coinduction" ident(R) simple_intropattern(H) :=
  match goal with
  | |- context [tower.gfp (cap ?B1 ?B2)] =>
      apply (proj1 (proj1 (weq_spec _ _) (gfp_b_uw B1 B2)))
  end; coinduction R H.



Section diacritical_rel.
Context {A : Type}.
Variable b1 b2 : mon (relation A).

Notation p := (progress_mon b1).
Notation a := (progress_mon b2).
#[local] Instance PR1 : Progress (progress_mon b1) := progress_mono b1.
#[local] Instance PR2 : Progress (progress_mon b2) := progress_mono b2.

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).
Notation w := (snd compan).
Notation UW := (b_uw b1 b2).

(* soundness of a technique, as a class, so it can be registered and found *)
Class ActiveUpto  (f : mon (relation A)) : Prop := active_upto_spec  : f <= w.
Class PassiveUpto (f : mon (relation A)) : Prop := passive_upto_spec : f <= u.

(* a passive technique is in particular an active one *)
#[export] Instance ActiveUpto_of_Passive (f : mon (relation A)) :
  PassiveUpto f -> ActiveUpto f.
Proof.
  intro Hf. unfold ActiveUpto.
  transitivity (fst (diacritical_companion.compan p a)).
  - exact Hf.
  - apply ucompan_below_wcompan; typeclasses eauto.
Qed.

(* the bridges, as subrelation instances on chain elements of [b_uw] *)
#[export] Instance sub_active_chain (f : mon (relation A)) {Hf : ActiveUpto f}
  (R : tower.Chain UW) : subrelation (f (tower.elem R)) (w (tower.elem R)).
Proof. exact (active_upto_spec (tower.elem R)). Qed.

#[export] Instance sub_passive_chain (f : mon (relation A)) {Hf : PassiveUpto f}
  (R : tower.Chain UW) : subrelation (f (tower.elem R)) (u (tower.elem R)).
Proof. exact (passive_upto_spec (tower.elem R)). Qed.

(* pairs already known bisimilar are usable in BOTH positions *)
#[export] Instance sub_disim_passive (R : tower.Chain UW) :
  subrelation (di_similarity p a) (u (tower.elem R)).
Proof. exact (disim_const_below_ucompan p a (tower.elem R)). Qed.

#[export] Instance sub_disim_active (R : tower.Chain UW) :
  subrelation (di_similarity p a) (w (tower.elem R)).
Proof. exact (disim_const_below_wcompan p a (tower.elem R)). Qed.

End diacritical_rel.

Arguments ActiveUpto {A} b1 b2 f.
Arguments PassiveUpto {A} b1 b2 f.


Tactic Notation "active_by" constr(f) ident(R) :=
  let Hw := fresh "Hw" in
  pose proof (sub_active_chain _ _ f R) as Hw; apply Hw; clear Hw.

Tactic Notation "passive_by" constr(f) ident(R) :=
  let Hu := fresh "Hu" in
  pose proof (sub_passive_chain _ _ f R) as Hu; apply Hu; clear Hu.

(* pairs already known bisimilar, in either position *)
Tactic Notation "bisim_passive" ident(R) :=
  let Hu := fresh "Hu" in
  pose proof (sub_disim_passive _ _ R) as Hu; apply Hu; clear Hu.

Tactic Notation "bisim_active" ident(R) :=
  let Hw := fresh "Hw" in
  pose proof (sub_disim_active _ _ R) as Hw; apply Hw; clear Hw.

Tactic Notation "di_upto" ident(x) ident(IH) :=
  apply leq_w_chain; apply leq_w_chain_ind; intros x IH; apply leq_snd_B_di.


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

(* for fusing inductive props in a step towards the diacritical theory *)
Goal forall P Q Q', (P -> Q) /\ (~P -> Q') -> (P /\ Q) \/ (~P /\ Q').  
intros. 
destruct (Classical_Prop.classic P).
left. destruct H. split. apply H0. apply H, H0. 
right. destruct H. split. apply H0. apply H1, H0. 
Qed. 

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

Section relation_lattice.
Context {A : Type}.
Notation Rel := (A -> A -> Prop).

Lemma rel_top   : (top : Rel) = fun _ _ => True.  Proof. reflexivity. Qed.
Lemma rel_bot   : (bot : Rel) = fun _ _ => False. Proof. reflexivity. Qed.
Lemma rel_cap (R S : Rel) : cap R S = fun x y => R x y /\ S x y. Proof. reflexivity. Qed.
Lemma rel_cup (R S : Rel) : cup R S = fun x y => R x y \/ S x y. Proof. reflexivity. Qed.
Lemma rel_leq (R S : Rel) : (R <= S) <-> (forall x y, R x y -> S x y).
Proof. split; intro H; exact H. Qed.

Lemma top_rel_refl (x : A) : (top : Rel) x x == True.
Proof. cbn. tauto. Qed.

End relation_lattice.


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

Lemma similarity_unfold x y :
  gfp sim x y <-> forall x', step x x' -> exists2 y', step y y' & gfp sim x' y'.
Proof. exact (gfp_fp sim x y). Qed.

Lemma eq_below_similarity : (fun a b : A => a = b) <= gfp sim.
Proof.
  apply leq_gfp. intros a b Hab a' Ha'.
  exists a'; [ rewrite <- Hab; exact Ha' | reflexivity ].
Qed.

Lemma similarity_refl x : gfp sim x x.
Proof. exact (eq_below_similarity x x eq_refl). Qed.

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

#[local] Instance Psim : Progress (progress_mon sim) := progress_mono sim.

Example similarity_passive_companion :
  fst (compan (progress_mon sim) (progress_mon sim)) == t sim.
Proof. exact (u_t sim). Qed.

  (* w's image is in the tower *)



End simulation.