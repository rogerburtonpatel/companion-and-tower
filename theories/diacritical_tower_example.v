(** * A concrete itree example for the diacritical companion + second-order tower

    This file grounds the abstract development ([experiments.v],
    [diacritical_redesign.v]) on real interaction trees.  Definitions of [itree]
    and [eqit] are pared down from InteractionTrees
    ([Core/ITreeDefinition.v], [Eq/Eqit.v]); everything else is phrased over
    THIS coinduction library ([mon]/[gfp] from [lattice]/[tower]) so the
    diacritical companion machinery applies verbatim.

    Road-map:
    - [Section itree]/[Section eqit]: minimal itrees and [eqit]
      ([eq_itree] = strong bisim, [eutt] = weak bisim up to tau).
    - [Section strong]: the passive/active split of STRONG bisimilarity
      ([g_p] owns tau, [g_a] owns the observable payload).  Its diacritical
      di-similarity is exactly [eq_itree] ([di_similarity_eq_itree]) -- a clean,
      fully-proved behavioural decomposition on real itrees.
    - the diacritical companion [(u,w)] of the split, and the SECOND-ORDER tower
      [B_di] instantiated at the itree relation lattice: [compan_gfp],
      [di_tower], [di_coinduction] all specialise for free.
    - [Section payoff]: concrete equivalences proved through the diacritical
      coinduction / tower principles.
    - [Section eutt_frontier]: the WEAK (tau-stripping) split.  BOTH directions
      are proved: [eutt_leq_disim] and, via the tau-closure reconstruction
      [meet_functor], [disim_leq_eutt] -- giving [disim_eq_eutt :
      di_similarity == eutt].  The crux is the case where the two halves strip
      tau on OPPOSITE sides; it is resolved by the strip lemmas, which are
      available precisely because a diacritical bisimulation satisfies both
      progressions.
    - [Section weak_diacritical]: consequently the whole stack (companion
      [(u,w)], second-order tower, diacritical coinduction) applies to WEAK
      bisimilarity; concrete payoff [eutt_tau : eutt (Tau t) t].
    - [Section upto_transitivity]: a concrete technique certified [sqr <= w]
      through the diacritical laws, plus [eq_itree_trans] (transitivity of
      strong bisimilarity) proved via the split.
    - [Section couple_fails] / [Section upto_eutt_fails] and the closing
      FINDING: why neither natural candidate is an active-only technique for a
      permissive-meet split, and what a split must satisfy to host one. *)

From Stdlib Require Import Utf8 Setoid Morphisms Program.Equality.
Require Import lattice progress evolution companion diacritical_companion tower.
Require Import tactics utils.
Require Import experiments.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(* ------------------------------------------------------------------------- *)
(** ** Interaction trees (minimal, from [ITreeDefinition.v]) *)

Section itree.
  Context {E : Type -> Type} {R : Type}.

  Variant itreeF (itree : Type) :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : Type} (e : E X) (k : X -> itree).

  CoInductive itree : Type := go { _observe : itreeF itree }.
End itree.

Arguments itree _ _ : clear implicits.
Arguments itreeF _ _ : clear implicits.

Notation itree' E R := (itreeF E R (itree E R)).
Definition observe {E R} (t : itree E R) : itree' E R := @_observe E R t.

Notation Ret x := (go (RetF x)).
Notation Tau t := (go (TauF t)).
Notation Vis e k := (go (VisF e k)).

Unset Contextual Implicit.
Unset Implicit Arguments.

(* ------------------------------------------------------------------------- *)
(** ** [eqit] (minimal, homogeneous), from [Eqit.v] *)

Local Coercion is_true : bool >-> Sortclass.

Section eqit.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Inductive eqitF (b1 b2 : bool) (sim : itree -> itree -> Prop) :
    itree' E R -> itree' E R -> Prop :=
  | EqRet r1 r2 (REL : RR r1 r2) : eqitF b1 b2 sim (RetF r1) (RetF r2)
  | EqTau m1 m2 (REL : sim m1 m2) : eqitF b1 b2 sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2 (REL : forall v, sim (k1 v) (k2 v)) :
      eqitF b1 b2 sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2 (CHECK : b1) (REL : eqitF b1 b2 sim (observe t1) ot2) :
      eqitF b1 b2 sim (TauF t1) ot2
  | EqTauR ot1 t2 (CHECK : b2) (REL : eqitF b1 b2 sim ot1 (observe t2)) :
      eqitF b1 b2 sim ot1 (TauF t2).

  Definition eqit_ (b1 b2 : bool) (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => eqitF b1 b2 sim (observe t1) (observe t2).

  Lemma eqitF_mono b1 b2 {sim sim' : itree -> itree -> Prop} (Hsim : sim <= sim') :
    eqitF b1 b2 sim <= eqitF b1 b2 sim'.
  Proof.
    intros ot1 ot2 H. induction H.
    - apply EqRet; assumption.
    - apply EqTau; apply Hsim; assumption.
    - apply EqVis; intro v; apply Hsim; apply REL.
    - apply EqTauL; assumption.
    - apply EqTauR; assumption.
  Qed.

  Lemma eqit__mono b1 b2 : Proper (leq ==> leq) (eqit_ b1 b2).
  Proof.
    intros sim sim' Hsim t1 t2 H. exact (@eqitF_mono b1 b2 sim sim' Hsim _ _ H).
  Qed.

  Definition eqit_mon (b1 b2 : bool) : mon (itree -> itree -> Prop) :=
    {| body := eqit_ b1 b2 ; Hbody := eqit__mono b1 b2 |}.

  Definition eqit (b1 b2 : bool) : itree -> itree -> Prop := gfp (eqit_mon b1 b2).

  Definition eq_itree : itree -> itree -> Prop := eqit false false.
  Definition eutt     : itree -> itree -> Prop := eqit true  true.

End eqit.

(* ------------------------------------------------------------------------- *)
(** ** The passive/active split of STRONG bisimilarity.

    [g_p] (passive) owns the tau structure (synchronised [Tau]s), and is
    permissive on the observable payload ([GpRet] relates any two [Ret]s,
    [GpVis] any two [Vis]es).  [g_a] (active) owns the payload ([GaRet] checks
    [RR], [GaVis] the continuations) and is permissive on tau.  Their MEET is
    exactly [eqit_ false false], so the diacritical di-similarity is [eq_itree]. *)

Section strong.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Inductive g_pF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | GpRet r1 r2 : g_pF sim (RetF r1) (RetF r2)
  | GpVis {u1} (e1 : E u1) k1 {u2} (e2 : E u2) k2 : g_pF sim (VisF e1 k1) (VisF e2 k2)
  | GpTau m1 m2 (REL : sim m1 m2) : g_pF sim (TauF m1) (TauF m2).

  Inductive g_aF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | GaRet r1 r2 (REL : RR r1 r2) : g_aF sim (RetF r1) (RetF r2)
  | GaVis {u} (e : E u) k1 k2 (REL : forall v, sim (k1 v) (k2 v)) : g_aF sim (VisF e k1) (VisF e k2)
  | GaTau m1 m2 : g_aF sim (TauF m1) (TauF m2).

  Lemma g_pF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : g_pF sim <= g_pF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply GpRet.
    - apply GpVis.
    - apply GpTau; apply H; assumption.
  Qed.

  Lemma g_aF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : g_aF sim <= g_aF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply GaRet; assumption.
    - apply GaVis; intro v; apply H; apply REL.
    - apply GaTau.
  Qed.

  Definition g_p_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => g_pF sim (observe t1) (observe t2).
  Definition g_a_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => g_aF sim (observe t1) (observe t2).

  Lemma g_p__mono : Proper (leq ==> leq) g_p_.
  Proof. intros sim sim' H t1 t2 He. exact (g_pF_mono H _ _ He). Qed.
  Lemma g_a__mono : Proper (leq ==> leq) g_a_.
  Proof. intros sim sim' H t1 t2 He. exact (g_aF_mono H _ _ He). Qed.

  Definition g_p : mon (itree -> itree -> Prop) := {| body := g_p_ ; Hbody := g_p__mono |}.
  Definition g_a : mon (itree -> itree -> Prop) := {| body := g_a_ ; Hbody := g_a__mono |}.

  #[local] Instance Pgp : Progress (progress_mon g_p) := progress_mono g_p.
  #[local] Instance Pga : Progress (progress_mon g_a) := progress_mono g_a.

  Lemma split_eqitF sim ot1 ot2 :
    (g_pF sim ot1 ot2 /\ g_aF sim ot1 ot2) <-> eqitF RR false false sim ot1 ot2.
  Proof.
    split.
    - intros [Hp Ha]. destruct Hp.
      + inversion Ha; subst. apply EqRet; assumption.
      + dependent destruction Ha. apply EqVis; assumption.
      + apply EqTau; assumption.
    - intro H. induction H.
      + split; [ apply GpRet | apply GaRet; assumption ].
      + split; [ apply GpTau; assumption | apply GaTau ].
      + split; [ apply GpVis | apply GaVis; assumption ].
      + discriminate CHECK.
      + discriminate CHECK.
  Qed.

  Theorem di_similarity_eq_itree :
    di_similarity (progress_mon g_p) (progress_mon g_a) == eq_itree RR.
  Proof.
    unfold eq_itree, eqit. apply antisym.
    - unfold di_similarity. apply sup_spec. intros S [H1 H2].
      apply leq_gfp. intros t1 t2 HS. apply split_eqitF. split.
      + exact (H1 t1 t2 HS).
      + exact (H2 t1 t2 HS).
    - unfold di_similarity. apply leq_xsup.
      pose proof (gfp_pfp (@eqit_mon E R RR false false)) as H. split.
      + intros t1 t2 Hg. specialize (H _ _ Hg).
        apply (split_eqitF _ (observe t1) (observe t2)) in H. exact (proj1 H).
      + intros t1 t2 Hg. specialize (H _ _ Hg).
        apply (split_eqitF _ (observe t1) (observe t2)) in H. exact (proj2 H).
  Qed.

End strong.

(* ------------------------------------------------------------------------- *)
(** ** The diacritical companion and second-order tower, on itrees.

    Everything from [experiments.v] specialises to the itree relation lattice
    by instantiating the abstract [b1 b2] with the concrete split [g_p g_a].
    The passive companion [u] and active companion [w] are now up-to techniques
    for STRONG bisimilarity; [compan_gfp] exhibits [(u,w)] as the greatest
    fixpoint of the second-order operator [B_di] on pairs of itree relations,
    so the whole tower theory ([di_tower], [di_chain_ind]) is available. *)

Section strong_diacritical.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Notation gp := (g_p (E:=E) (R:=R)).
  Notation ga := (g_a (E:=E) RR).
  #[local] Instance Pgp' : Progress (progress_mon gp) := progress_mono gp.
  #[local] Instance Pga' : Progress (progress_mon ga) := progress_mono ga.

  Notation compan := (diacritical_companion.compan (progress_mon gp) (progress_mon ga)).
  Notation u := (fst compan).
  Notation w := (snd compan).

  (* the diacritical di-similarity of the split is strong bisimilarity *)
  Corollary companion_bisim :
    di_similarity (progress_mon gp) (progress_mon ga) == eq_itree RR.
  Proof. apply di_similarity_eq_itree. Qed.

  (* SECOND-ORDER TOWER: [(u,w)] is a gfp of [B_di] on the pair lattice
     [L_lift (itree -> itree -> Prop)] -- the itree instance of [compan_gfp]. *)
  Corollary itree_compan_gfp : compan == tower.gfp (experiments.B_di gp ga).
  Proof. apply (experiments.compan_gfp gp ga). Qed.

  (* Both up-to companions sit below the ordinary companion of the PASSIVE
     behaviour ([u_below_t1]/[w_below_t1] at the itree lattice). *)
  Corollary itree_w_below_passive : w <= companion.t gp.
  Proof. apply (experiments.w_below_t1 gp ga). Qed.
  Corollary itree_u_below_passive : u <= companion.t gp.
  Proof. apply (experiments.u_below_t1 gp ga). Qed.

  (* Diacritical coinduction into strong bisimilarity: progress passively via
     [u] and actively via [w].  [gfp (cap gp ga)] IS [eq_itree] here. *)
  Corollary itree_di_coinduction (S : itree -> itree -> Prop)
    (Hp : S <= gp (u S)) (Ha : S <= ga (w S)) : S <= eq_itree RR.
  Proof.
    rewrite <- companion_bisim.
    apply (diacritical_companion.soundness (progress_mon gp) (progress_mon ga)); assumption.
  Qed.

  (* SECOND-ORDER TOWER INDUCTION on itrees: an inf-closed invariant on pairs
     of itree relations, preserved by one [B_di]-step, holds of the companion
     pair [(u,w)] -- the itree instance of [di_tower]. *)
  Corollary itree_di_tower (Q : L_lift (itree -> itree -> Prop) -> Prop)
    (HQ : Proper (weq ==> Basics.impl) Q) (Hinf : inf_closed Q)
    (Hstep : forall x : Chain (experiments.B_di gp ga),
               Q (elem x) -> Q (experiments.B_di gp ga (elem x))) :
    Q compan.
  Proof. apply (experiments.di_tower gp ga); assumption. Qed.

End strong_diacritical.

(* ------------------------------------------------------------------------- *)
(** ** Payoff: concrete strong-bisimilarity facts, diacritically.

    The diagonal is a DIACRITICAL bisimulation: it self-progresses both
    passively ([g_p]: heads match, taus recurse) and actively ([g_a]: [RR] at
    [Ret], continuations at [Vis]).  So it sits below [di_similarity], i.e.
    below [eq_itree] -- reflexivity of strong bisimilarity, read off the split. *)

Section payoff.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop) (Hrefl : forall r, RR r r).
  Notation itree := (itree E R).
  Notation gp := (g_p (E:=E) (R:=R)).
  Notation ga := (g_a (E:=E) RR).
  #[local] Instance Pgp2 : Progress (progress_mon gp) := progress_mono gp.
  #[local] Instance Pga2 : Progress (progress_mon ga) := progress_mono ga.

  (* The diagonal is a passive and an active bisimulation, checked on the
     observed head (a bound [ot], so case analysis is clean). *)
  Lemma g_pF_diag (ot : itree' E R) : g_pF (fun t t' : itree => t = t') ot ot.
  Proof. destruct ot as [r | m | X e k]. - apply GpRet. - apply GpTau; reflexivity. - apply GpVis. Qed.
  Lemma g_aF_diag (ot : itree' E R) : g_aF RR (fun t t' : itree => t = t') ot ot.
  Proof. destruct ot as [r | m | X e k]. - apply GaRet, Hrefl. - apply GaTau. - apply GaVis; reflexivity. Qed.

  Lemma diag_below_eq_itree : (fun t t' : itree => t = t') <= eq_itree RR.
  Proof.
    rewrite <- companion_bisim. apply leq_xsup. split.
    - intros t t' <-. exact (g_pF_diag (observe t)).
    - intros t t' <-. exact (g_aF_diag (observe t)).
  Qed.

  Corollary eq_itree_refl (t : itree) : eq_itree RR t t.
  Proof. apply diag_below_eq_itree. reflexivity. Qed.

End payoff.

(* ------------------------------------------------------------------------- *)
(** ** A CONCRETE TECHNIQUE certified [<= w]: up-to-transitivity.

    [experiments.f_below_w] reduces "[f] is a sound ACTIVE up-to technique"
    (taking the strong partner to [bot]) to two [f]-laws.  We discharge them for
    up-to-transitivity [sqr S = S o S] on the strong split. *)

Section upto_transitivity.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop)
          (RRtrans : forall r1 r2 r3, RR r1 r2 -> RR r2 r3 -> RR r1 r3).
  Notation itree := (itree E R).
  Notation Rel := (itree -> itree -> Prop).
  Notation gp := (g_p (E:=E) (R:=R)).
  Notation ga := (g_a (E:=E) RR).
  #[local] Instance Pgp3 : Progress (progress_mon gp) := progress_mono gp.
  #[local] Instance Pga3 : Progress (progress_mon ga) := progress_mono ga.
  Notation compan := (diacritical_companion.compan (progress_mon gp) (progress_mon ga)).
  Notation w := (snd compan).

  Program Definition sqr : mon Rel :=
    {| body S := fun t1 t2 => exists t3, S t1 t3 /\ S t3 t2 |}.
  Next Obligation. intros S S' HS t1 t2 [t3 [H1 H2]]. exists t3. split; apply HS; assumption. Qed.

  (* the two halves compose; note the middle head-shape is forced to agree,
     which is exactly why there is no tau-alignment problem in the STRONG split *)
  Lemma g_pF_trans {S : Rel} {ot1 ot2 ot3} :
    g_pF S ot1 ot2 -> g_pF S ot2 ot3 -> g_pF (sqr S) ot1 ot3.
  Proof.
    intros D1 D2. destruct D1.
    - inversion D2; subst. apply GpRet.
    - inversion D2; subst. apply GpVis.
    - inversion D2; subst. apply GpTau. exists m2. split; assumption.
  Qed.

  Lemma g_aF_trans {S : Rel} {ot1 ot2 ot3} :
    g_aF RR S ot1 ot2 -> g_aF RR S ot2 ot3 -> g_aF RR (sqr S) ot1 ot3.
  Proof.
    intros D1 D2. destruct D1.
    - inversion D2; subst. apply GaRet. eapply RRtrans; eassumption.
    - dependent destruction D2. apply GaVis. intro v.
      eexists. split; [ apply REL | apply REL0 ].
    - inversion D2; subst. apply GaTau.
  Qed.

  (* PASSIVE law (unconditional) *)
  Lemma sqr_passive : evolution (progress_mon gp) sqr sqr.
  Proof.
    constructor. intros S1 S2 H t1 t2 [t3 [H1 H2]].
    exact (g_pF_trans (H t1 t3 H1) (H t3 t2 H2)).
  Qed.

  (* ACTIVE law (conditional; the premise happens to be unnecessary here) *)
  Lemma sqr_active : r_evolution (progress_mon gp) (progress_mon ga) sqr sqr.
  Proof.
    constructor. intros S1 S2 _ H t1 t2 [t3 [H1 H2]].
    exact (g_aF_trans (H t1 t3 H1) (H t3 t2 H2)).
  Qed.

  Theorem sqr_below_w : sqr <= w.
  Proof. exact (experiments.f_below_w gp ga sqr sqr_passive sqr_active). Qed.

  (* PAYOFF: strong bisimilarity is transitive, via the diacritical split.
     [sqr (eq_itree RR)] is exhibited as a DIACRITICAL bisimulation. *)
  Lemma eq_itree_step :
    eq_itree RR <= gp (eq_itree RR) /\ eq_itree RR <= ga (eq_itree RR).
  Proof.
    split; intros s1 s2 Hs;
      pose proof (gfp_pfp (@eqit_mon E R RR false false) s1 s2 Hs) as Hd;
      apply (split_eqitF RR _ (observe s1) (observe s2)) in Hd; apply Hd.
  Qed.

  Theorem eq_itree_trans (t1 t2 t3 : itree) :
    eq_itree RR t1 t2 -> eq_itree RR t2 t3 -> eq_itree RR t1 t3.
  Proof.
    intros H1 H2. destruct eq_itree_step as [Hp Ha].
    assert (Hds : sqr (eq_itree RR) <= di_similarity (progress_mon gp) (progress_mon ga)).
    { apply leq_xsup. split.
      - intros s1 s2 [s3 [Q1 Q2]]. exact (g_pF_trans (Hp s1 s3 Q1) (Hp s3 s2 Q2)).
      - intros s1 s2 [s3 [Q1 Q2]]. exact (g_aF_trans (Ha s1 s3 Q1) (Ha s3 s2 Q2)). }
    pose proof (@di_similarity_eq_itree E R RR) as Heq.
    apply weq_spec in Heq. destruct Heq as [Hle _].
    apply Hle. apply Hds. exists t2. split; assumption.
  Qed.

End upto_transitivity.

(* ------------------------------------------------------------------------- *)
(** ** WEAK bisimilarity (eutt) splits diacritically -- both directions.

    The interesting active-only techniques live over WEAK bisimilarity, where
    tau is silent.  The split now has each half strip tau ITSELF ([BpTauL/R],
    [BaTauL/R]): [b_p] owns [Ret] (checks [RR]) + tau, permissive on [Vis];
    [b_a] owns [Vis] (checks continuations) + tau, permissive on [Ret].

    Both directions are proved here:
    - [eutt_leq_disim]: eutt is a diacritical bisimulation (easy direction);
    - [disim_leq_eutt]: every diacritical bisimulation is a eutt-bisimulation.
      This is the genuine TAU-CLOSURE RECONSTRUCTION ([meet_functor]) -- the
      case where the two halves strip tau on OPPOSITE sides, which the naive
      destruction cannot handle.  The resolution: a diacritical bisimulation
      [sim] satisfies BOTH progressions, which makes the four tau-strip lemmas
      ([bpF_strip_TauL/R], [baF_strip_TauL/R]) provable; a strip lemma then
      re-aligns the mismatched derivation so the induction hypothesis applies.
    Together: [disim_eq_eutt : di_similarity == eutt].  So the whole diacritical
    stack -- companion [(u,w)], second-order tower, diacritical coinduction --
    applies to WEAK bisimilarity, where the active-only techniques live. *)

Section eutt_frontier.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Inductive b_pF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | BpRet r1 r2 (REL : RR r1 r2) : b_pF sim (RetF r1) (RetF r2)
  | BpVis {u1} (e1 : E u1) k1 {u2} (e2 : E u2) k2 : b_pF sim (VisF e1 k1) (VisF e2 k2)
  | BpTau m1 m2 (REL : sim m1 m2) : b_pF sim (TauF m1) (TauF m2)
  | BpTauL t1 ot2 (REL : b_pF sim (observe t1) ot2) : b_pF sim (TauF t1) ot2
  | BpTauR ot1 t2 (REL : b_pF sim ot1 (observe t2)) : b_pF sim ot1 (TauF t2).

  Inductive b_aF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | BaRet r1 r2 : b_aF sim (RetF r1) (RetF r2)
  | BaVis {u} (e : E u) k1 k2 (REL : forall v, sim (k1 v) (k2 v)) : b_aF sim (VisF e k1) (VisF e k2)
  | BaTau m1 m2 (REL : sim m1 m2) : b_aF sim (TauF m1) (TauF m2)
  | BaTauL t1 ot2 (REL : b_aF sim (observe t1) ot2) : b_aF sim (TauF t1) ot2
  | BaTauR ot1 t2 (REL : b_aF sim ot1 (observe t2)) : b_aF sim ot1 (TauF t2).

  Lemma eutt_below_bp sim : eqitF RR true true sim <= b_pF sim.
  Proof.
    intros ot1 ot2 H. induction H.
    - apply BpRet; assumption.
    - apply BpTau; assumption.
    - apply BpVis.
    - apply BpTauL; assumption.
    - apply BpTauR; assumption.
  Qed.

  Lemma eutt_below_ba sim : eqitF RR true true sim <= b_aF sim.
  Proof.
    intros ot1 ot2 H. induction H.
    - apply BaRet.
    - apply BaTau; assumption.
    - apply BaVis; assumption.
    - apply BaTauL; assumption.
    - apply BaTauR; assumption.
  Qed.

  Lemma b_pF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : b_pF sim <= b_pF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply BpRet; assumption.
    - apply BpVis.
    - apply BpTau; apply H; assumption.
    - apply BpTauL; assumption.
    - apply BpTauR; assumption.
  Qed.
  Lemma b_aF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : b_aF sim <= b_aF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply BaRet.
    - apply BaVis; intro v; apply H; apply REL.
    - apply BaTau; apply H; assumption.
    - apply BaTauL; assumption.
    - apply BaTauR; assumption.
  Qed.

  Definition b_p_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => b_pF sim (observe t1) (observe t2).
  Definition b_a_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => b_aF sim (observe t1) (observe t2).
  Lemma b_p__mono : Proper (leq ==> leq) b_p_.
  Proof. intros sim sim' H t1 t2 He. exact (b_pF_mono H _ _ He). Qed.
  Lemma b_a__mono : Proper (leq ==> leq) b_a_.
  Proof. intros sim sim' H t1 t2 He. exact (b_aF_mono H _ _ He). Qed.
  Definition b_p : mon (itree -> itree -> Prop) := {| body := b_p_ ; Hbody := b_p__mono |}.
  Definition b_a : mon (itree -> itree -> Prop) := {| body := b_a_ ; Hbody := b_a__mono |}.
  #[local] Instance Pbp : Progress (progress_mon b_p) := progress_mono b_p.
  #[local] Instance Pba : Progress (progress_mon b_a) := progress_mono b_a.

  (* SOUND direction: eutt is a diacritical bisimulation of the weak split.
     Unfold eutt once ([gfp_pfp]) and refine into each half. *)
  Theorem eutt_leq_disim :
    eutt RR <= di_similarity (progress_mon b_p) (progress_mon b_a).
  Proof.
    apply leq_xsup. split; intros t1 t2 H.
    - apply eutt_below_bp. exact (gfp_pfp (eqit_mon RR true true) t1 t2 H).
    - apply eutt_below_ba. exact (gfp_pfp (eqit_mon RR true true) t1 t2 H).
  Qed.

  (* --- tau-strip lemmas: when [sim] is a bisimulation, a tau on either side can
     be pushed into the derivation.  The synchronised-tau case ([BpTau]/[BaTau])
     is exactly where the bisimulation hypothesis unfolds [sim] -- WITHOUT it
     these are false, which is why the reconstruction needs a bisimulation. --- *)
  Lemma bpF_strip_TauR {sim : itree -> itree -> Prop}
    (Hsp : forall t1 t2, sim t1 t2 -> b_pF sim (observe t1) (observe t2)) :
    forall os1 ot2, b_pF sim os1 ot2 -> forall t2, ot2 = TauF t2 -> b_pF sim os1 (observe t2).
  Proof.
    intros os1 ot2 H.
    induction H as [ r1 r2 HRR | u1 e1 k1 u2 e2 k2 | m1 m2 REL | t1 o2 REL IH | o1 t2 REL IH ];
      intros tt2 Heq; try discriminate.
    - inversion Heq; subst. apply BpTauL. apply Hsp. exact REL.
    - apply BpTauL. exact (IH tt2 Heq).
    - inversion Heq; subst. exact REL.
  Qed.

  Lemma bpF_strip_TauL {sim : itree -> itree -> Prop}
    (Hsp : forall t1 t2, sim t1 t2 -> b_pF sim (observe t1) (observe t2)) :
    forall os1 ot2, b_pF sim os1 ot2 -> forall t1, os1 = TauF t1 -> b_pF sim (observe t1) ot2.
  Proof.
    intros os1 ot2 H.
    induction H as [ r1 r2 HRR | u1 e1 k1 u2 e2 k2 | m1 m2 REL | t1 o2 REL IH | o1 t2 REL IH ];
      intros tt1 Heq; try discriminate.
    - inversion Heq; subst. apply BpTauR. apply Hsp. exact REL.
    - inversion Heq; subst. exact REL.
    - apply BpTauR. exact (IH tt1 Heq).
  Qed.

  Lemma baF_strip_TauR {sim : itree -> itree -> Prop}
    (Hsa : forall t1 t2, sim t1 t2 -> b_aF sim (observe t1) (observe t2)) :
    forall os1 ot2, b_aF sim os1 ot2 -> forall t2, ot2 = TauF t2 -> b_aF sim os1 (observe t2).
  Proof.
    intros os1 ot2 H.
    induction H as [ r1 r2 | u e k1 k2 REL | m1 m2 REL | t1 o2 REL IH | o1 t2 REL IH ];
      intros tt2 Heq; try discriminate.
    - inversion Heq; subst. apply BaTauL. apply Hsa. exact REL.
    - apply BaTauL. exact (IH tt2 Heq).
    - inversion Heq; subst. exact REL.
  Qed.

  Lemma baF_strip_TauL {sim : itree -> itree -> Prop}
    (Hsa : forall t1 t2, sim t1 t2 -> b_aF sim (observe t1) (observe t2)) :
    forall os1 ot2, b_aF sim os1 ot2 -> forall t1, os1 = TauF t1 -> b_aF sim (observe t1) ot2.
  Proof.
    intros os1 ot2 H.
    induction H as [ r1 r2 | u e k1 k2 REL | m1 m2 REL | t1 o2 REL IH | o1 t2 REL IH ];
      intros tt1 Heq; try discriminate.
    - inversion Heq; subst. apply BaTauR. apply Hsa. exact REL.
    - inversion Heq; subst. exact REL.
    - apply BaTauR. exact (IH tt1 Heq).
  Qed.

  (* THE RECONSTRUCTION (the tau-closure lemma the sandbox left admitted): for a
     bisimulation [sim], the meet of the two halves refines eutt's functor.  The
     tau cross-cases (strip on OPPOSITE sides) are the crux -- resolved by
     re-aligning with a strip lemma, then feeding the induction hypothesis. *)
  Lemma meet_functor {sim : itree -> itree -> Prop}
    (Hsp : forall t1 t2, sim t1 t2 -> b_pF sim (observe t1) (observe t2))
    (Hsa : forall t1 t2, sim t1 t2 -> b_aF sim (observe t1) (observe t2)) :
    forall ot1 ot2, b_pF sim ot1 ot2 -> b_aF sim ot1 ot2 -> eqitF RR true true sim ot1 ot2.
  Proof.
    intros ot1 ot2 Hp.
    induction Hp as [ r1 r2 HRR | u1 e1 k1 u2 e2 k2 | m1 m2 REL | t1 o2 REL IH | o1 t2 REL IH ];
      intros Hba.
    - apply EqRet. exact HRR.
    - dependent destruction Hba. apply EqVis. exact REL.
    - apply EqTau. exact REL.
    - (* BpTauL: ot1 = TauF t1 *)
      inversion Hba; subst.
      + (* BaTau: synchronised tau *) apply EqTau; assumption.
      + (* BaTauL: both strip left *) apply EqTauL; [ reflexivity | apply IH; assumption ].
      + (* BaTauR: OPPOSITE strip -- re-align via strip lemma, feed IH *)
        apply EqTauL; [ reflexivity | ].
        apply IH. apply BaTauR. eapply (baF_strip_TauL Hsa); [ eassumption | reflexivity ].
    - (* BpTauR: ot2 = TauF t2 *)
      inversion Hba; subst.
      + (* BaTau *) apply EqTau; assumption.
      + (* BaTauL: OPPOSITE strip *)
        apply EqTauR; [ reflexivity | ].
        apply IH. apply BaTauL. eapply (baF_strip_TauR Hsa); [ eassumption | reflexivity ].
      + (* BaTauR: both strip right *) apply EqTauR; [ reflexivity | apply IH; assumption ].
  Qed.

  (* HARD DIRECTION: every diacritical bisimulation of the weak split is a
     eutt-bisimulation.  The witness [sim] IS a bisimulation, so [meet_functor]
     applies.  With [eutt_leq_disim] this gives [di_similarity == eutt]. *)
  Theorem disim_leq_eutt :
    di_similarity (progress_mon b_p) (progress_mon b_a) <= eutt RR.
  Proof.
    unfold eutt, eqit. apply leq_gfp. intros t1 t2 Hds.
    destruct Hds as [sim [Hbp Hba] H].
    assert (Hsub : sim <= di_similarity (progress_mon b_p) (progress_mon b_a))
      by (apply leq_xsup; split; assumption).
    apply (eqitF_mono RR true true Hsub).
    apply (meet_functor Hbp Hba).
    - exact (Hbp t1 t2 H).
    - exact (Hba t1 t2 H).
  Qed.

  (* The weak split's diacritical di-similarity is EXACTLY weak bisimilarity. *)
  Theorem disim_eq_eutt :
    di_similarity (progress_mon b_p) (progress_mon b_a) == eutt RR.
  Proof. apply antisym; [ apply disim_leq_eutt | apply eutt_leq_disim ]. Qed.

End eutt_frontier.

(* ------------------------------------------------------------------------- *)
(** ** Why the passive functor is NOT itself active-only (couple fails).

    The abstract [experiments.b1_active_only] proves [b1 <= w] from the coupling
    law [couple : R <= b1 R -> R <= b2 S -> b1 R <= b2 (b1 S)].  On a real
    bisimulation split this law is FALSE: the passive functor [b_p] is permissive
    on the active concern (it relates two [Vis]es with DIFFERENT events), whereas
    the active [b_a] demands matching events.  So [b_p R] contains pairs that
    [b_a (b_p S)] rejects.  We exhibit this concretely with two events [0 <> 1].

    Hence [b_p] is not a sound active enhancement; the genuinely active-only
    techniques (up-to-eutt, up-to-transitivity) are the ones whose soundness
    needs the tau-closure reconstruction above -- that is where the diacritical
    tower does real work beyond the reach of ordinary compatibility. *)

Section couple_fails.
  Notation NatE := (fun _ : Type => nat).
  Notation itN := (itree NatE nat).
  Definition k0 : unit -> itN := fun _ => Ret 0.

  Notation bp := (@b_p NatE nat (@eq nat)).
  Notation ba := (@b_a NatE nat).

  Remark couple_fails_weak :
    ~ (forall R S : itN -> itN -> Prop,
          R <= bp R -> R <= ba S -> bp R <= ba (bp S)).
  Proof.
    intro H. specialize (H bot bot (leq_bx _) (leq_bx _)).
    assert (Hp : bp bot (Vis (0 : NatE unit) k0) (Vis (1 : NatE unit) k0)) by apply BpVis.
    apply H in Hp. inversion Hp.
  Qed.

End couple_fails.

(* ------------------------------------------------------------------------- *)
(** ** The diacritical companion for WEAK bisimilarity, and an ACTIVE-ONLY
       up-to technique.

    [disim_eq_eutt] licenses the whole stack over eutt.  We now exhibit a
    technique that is sound in ACTIVE position but NOT a compatible up-to
    technique for the passive behaviour: "up-to tau on the right" [tauR].

    [tauR R] relates [t1] to [t2] whenever [R] relates [t1] to [Tau t2] -- i.e.
    it lets a proof insert a tau on the right.  This is:
    - sound for the ACTIVE half: [b_a] strips tau itself ([BaTauR]);
    - UNSOUND as an ordinary (passive-strength) technique in the sense that it is
      NOT [b_p]-compatible for arbitrary relations -- see [tauR_not_compat]. *)

Section weak_diacritical.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).
  Notation bp := (@b_p E R RR).
  Notation ba := (@b_a E R).
  #[local] Instance Pbp' : Progress (progress_mon bp) := progress_mono bp.
  #[local] Instance Pba' : Progress (progress_mon ba) := progress_mono ba.

  Notation compan := (diacritical_companion.compan (progress_mon bp) (progress_mon ba)).
  Notation u := (fst compan).
  Notation w := (snd compan).

  (* the diacritical di-similarity of the weak split is eutt *)
  Corollary weak_companion_eutt :
    di_similarity (progress_mon bp) (progress_mon ba) == eutt RR.
  Proof. apply disim_eq_eutt. Qed.

  (* the second-order tower, now for eutt *)
  Corollary weak_compan_gfp : compan == tower.gfp (experiments.B_di bp ba).
  Proof. apply (experiments.compan_gfp bp ba). Qed.

  (* DIACRITICAL COINDUCTION INTO EUTT: progress passively via [u], actively via
     [w], and land in weak bisimilarity. *)
  Corollary eutt_di_coinduction (S : itree -> itree -> Prop)
    (Hp : S <= bp (u S)) (Ha : S <= ba (w S)) : S <= eutt RR.
  Proof.
    rewrite <- weak_companion_eutt.
    apply (diacritical_companion.soundness (progress_mon bp) (progress_mon ba)); assumption.
  Qed.

  (* --- concrete payoff: tau-absorption, [eutt (Tau t) t] ---

     Proved by exhibiting a DIACRITICAL bisimulation: the relation "left is one
     tau ahead of right, or they are equal".  It self-progresses in BOTH halves,
     hence lies in [di_similarity] = [eutt] ([weak_companion_eutt]).  Note each
     half absorbs the tau with its OWN strip rule ([BpTauL] / [BaTauL]) -- this
     is exactly the structure the reconstruction validates. *)
  Hypothesis Hrefl : forall r, RR r r.

  Definition tau_ahead : itree -> itree -> Prop :=
    fun t1 t2 => t1 = t2 \/ observe t1 = TauF t2 \/ observe t2 = TauF t1.

  Lemma tau_ahead_diag_p (ot : itree' E R) : b_pF RR tau_ahead ot ot.
  Proof.
    destruct ot as [ r | m | X e k ].
    - apply BpRet, Hrefl.
    - apply BpTau. left. reflexivity.
    - apply BpVis.
  Qed.

  Lemma tau_ahead_diag_a (ot : itree' E R) : b_aF tau_ahead ot ot.
  Proof.
    destruct ot as [ r | m | X e k ].
    - apply BaRet.
    - apply BaTau. left. reflexivity.
    - apply BaVis. intro v. left. reflexivity.
  Qed.

  Lemma tau_ahead_below_eutt : tau_ahead <= eutt RR.
  Proof.
    rewrite <- weak_companion_eutt. apply leq_xsup. split.
    - intros t1 t2 [<- | [Ht | Ht]]; cbn; unfold b_p_.
      + apply tau_ahead_diag_p.
      + rewrite Ht. apply BpTauL. apply tau_ahead_diag_p.
      + rewrite Ht. apply BpTauR. apply tau_ahead_diag_p.
    - intros t1 t2 [<- | [Ht | Ht]]; cbn; unfold b_a_.
      + apply tau_ahead_diag_a.
      + rewrite Ht. apply BaTauL. apply tau_ahead_diag_a.
      + rewrite Ht. apply BaTauR. apply tau_ahead_diag_a.
  Qed.

  (* tau is silent for weak bisimilarity -- through the diacritical companion. *)
  Theorem eutt_tau (t : itree) : eutt RR (Tau t) t.
  Proof. apply tau_ahead_below_eutt. right. left. reflexivity. Qed.

  Theorem eutt_tau' (t : itree) : eutt RR t (Tau t).
  Proof. apply tau_ahead_below_eutt. right. right. reflexivity. Qed.

  Corollary eutt_refl (t : itree) : eutt RR t t.
  Proof. apply tau_ahead_below_eutt. left. reflexivity. Qed.

  (* STATUS of genuinely active-only techniques over eutt.

     The stack above is now fully available for eutt, so a technique [f] is a
     sound ACTIVE up-to as soon as [f <= w], for which [experiments.f_below_w]
     asks only two [f]-laws (strong partner [bot]).  What remains OPEN here is
     exhibiting a concrete [f] that is [<= w] but NOT below the ordinary
     companion [t (bp cap ba)].

     Two natural candidates provably FAIL, for the same structural reason --
     each functor is PERMISSIVE on the other's concern:
     - [bp] as an active technique: refuted by [couple_fails_weak] below
       ([bp] relates two [Vis]es with different events; [ba] rejects them);
     - [ba] as a passive technique: symmetric ([ba] relates any two [Ret]s,
       [bp] demands [RR]).
     A working candidate must therefore be a closure that exploits the active
     law's premise [R <= bp R] itself (up-to-eutt / up-to-transitivity), whose
     soundness needs transitivity of eutt -- a further ITree-scale development.
     The machinery to certify it, once formulated, is complete and in place. *)

End weak_diacritical.

(* ------------------------------------------------------------------------- *)
(** ** Is the CLASSIC active-only technique (up-to-eutt) below [w] here?  NO.

    Up-to-weak-bisimilarity is the textbook technique that is unsound in general
    but sound in active position -- exactly what [w] is meant to license.  But
    [f <= w] requires (via [pev_weak], which is UNCONDITIONAL) that [f] be
    [b_p]-compatible, and up-to-eutt is not.  Counterexample below. *)

Section upto_eutt_fails.
  Notation NatE := (fun _ : Type => nat).
  Notation itN := (itree NatE nat).
  Notation bp := (@b_p NatE nat (@eq nat)).
  Notation eqn := (@eq nat).

  Definition eutt_clo (S : itN -> itN -> Prop) : itN -> itN -> Prop :=
    fun t1 t2 => exists s1 s2, eutt eqn t1 s1 /\ S s1 s2 /\ eutt eqn s2 t2.

  Definition Rbad : itN -> itN -> Prop :=
    fun t1 t2 => t1 = Tau (Ret 0) /\ t2 = Tau (Ret 1).
  Definition Sbad : itN -> itN -> Prop :=
    fun t1 t2 => t1 = Ret 0 /\ t2 = Ret 1.

  Lemma Rbad_step : Rbad <= bp Sbad.
  Proof. intros t1 t2 [-> ->]. cbn. unfold b_p_. apply BpTau. split; reflexivity. Qed.

  (* [Ret 0] and [Ret 1] are in the eutt-closure of [Rbad]: absorb one tau on
     each side ([eutt_tau'] / [eutt_tau]). *)
  Lemma bad_in_clo : eutt_clo Rbad (Ret 0) (Ret 1).
  Proof.
    exists (Tau (Ret 0)), (Tau (Ret 1)). split; [ | split ].
    - apply (@eutt_tau' NatE nat eqn (fun r => eq_refl)).
    - split; reflexivity.
    - apply (@eutt_tau NatE nat eqn (fun r => eq_refl)).
  Qed.

  (* ...but [b_p] demands [RR] at a Ret frontier, and [0 <> 1]. *)
  Theorem upto_eutt_not_bp_compatible :
    ~ (forall S1 S2 : itN -> itN -> Prop, S1 <= bp S2 -> eutt_clo S1 <= bp (eutt_clo S2)).
  Proof.
    intro H. pose proof (H Rbad Sbad Rbad_step (Ret 0) (Ret 1) bad_in_clo) as Hbad.
    cbn in Hbad. unfold b_p_ in Hbad. inversion Hbad. discriminate REL.
  Qed.

End upto_eutt_fails.

(* ------------------------------------------------------------------------- *)
(** * FINDING: what an active-only technique must look like, and why neither
      candidate qualifies for a permissive-meet split.

    [f <= w] is established by [experiments.f_below_w] from two laws:
      (P) [pev_weak]  [evolution p f f]     -- UNCONDITIONAL b_p-compatibility;
      (A) [aev_weak]  [r_evolution p a f f] -- b_a-compatibility, CONDITIONAL on
                                               the premise [R <= b_p R].
    (P) is unconditional even when the strong partner is [bot], so:

      *** every [f <= w] is fully b_p-compatible, hence [w <= t b_p]. ***

    (this is [itree_w_below_passive] / [experiments.w_below_t1]).  So the extra
    power of [w] over the ordinary companion [t (b_p cap b_a)] is located in
    exactly ONE place: the b_a law may use the premise.  An active-only
    technique must therefore be b_p-compatible, and b_a-compatible only
    conditionally.  Both natural candidates provably fail one of the two:

    - up-to-eutt (the textbook active-only technique) fails (P):
      [upto_eutt_not_bp_compatible].  Absorbing a tau on each side moves a Ret
      frontier past a synchronised-tau step ([BpTau]), and [b_p] then demands
      [RR] where none is available.  This is not a defect of the proof but of
      the split: [b_p] has a stopping [BpTau] rule, so it is not eutt-closed.
    - the passive functor [b_p] itself fails (A): [couple_fails_weak].  It
      relates two [Vis] nodes with different events (it is PERMISSIVE on the
      active concern), which [b_a] rejects -- and the premise, which constrains
      [R], cannot repair pairs that [f] manufactures out of [R].

    The second failure is structural for ANY permissive-meet split: each half is
    permissive exactly on the concern the other half checks, so a technique
    built from one half always manufactures pairs the other rejects, and a
    premise on [R] has no purchase on them.  Realising the diacritical extra
    power therefore needs a split whose PASSIVE functor is already closed under
    the equivalence being enhanced (so that (P) is free), rather than merely
    permissive on the active concern.  That is the next design step; the
    certification machinery for it ([f_below_w], and [sqr_below_w] as a worked
    instance) is complete and in place. *)
