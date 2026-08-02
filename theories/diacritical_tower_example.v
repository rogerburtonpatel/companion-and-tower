(** * Interaction trees for the diacritical companion and its second-order tower

    Grounds the abstract development ([experiments.v], [diacritical_redesign.v])
    on real interaction trees.  [itree] and [eqit] are pared down from
    InteractionTrees ([Core/ITreeDefinition.v], [Eq/Eqit.v]); everything else is
    phrased over THIS library ([mon]/[gfp] from [lattice]/[tower]), so the
    diacritical machinery applies verbatim.

    A behaviour is split into a PASSIVE and an ACTIVE progression whose meet is
    the equivalence of interest.  The diacritical companion [(u,w)] of that pair
    supplies coinduction ([soundness]) and, being itself a greatest fixpoint on
    the lattice of PAIRS of relations, a second-order tower.

    - [Section strong]: the split of STRONG bisimilarity -- [g_p] owns tau,
      [g_a] owns the observable payload; [di_similarity_eq_itree] shows the meet
      is exactly [eq_itree].
    - [Section strong_diacritical]: the companion, the second-order tower
      ([itree_compan_gfp], [itree_di_tower]) and diacritical coinduction,
      instantiated at the itree relation lattice.
    - [Section payoff]: [eq_itree_refl], read off the split.
    - [Section upto_transitivity]: up-to-transitivity certified [sqr <= w] both
      by coinduction ([sqr_below_w]) and by SECOND-ORDER TOWER INDUCTION
      ([sqr_below_w_tower], via [experiments.f_below_w_tower]), plus
      [eq_itree_trans].
    - [Section weak]: the same for WEAK bisimilarity.  The passive half owns tau
      ONLY (permissive at both frontiers); the active half is the full eutt
      functor, so the Ret and Vis obligations -- the cases in which up-to-eutt is
      valid -- both sit on the active side. *)

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
     of itree relations, preserved by one [B_di]-step, holds at the gfp of
     [B_di] -- the itree instance of [experiments.di_tower_gfp].  No [Proper]
     side-condition: the gfp is itself a chain element.  Crossing to the
     companion pair, when needed, is the order fact
     [experiments.gfp_B_di_below_compan]. *)
  Corollary itree_di_tower (Q : L_lift (itree -> itree -> Prop) -> Prop)
    (Hinf : inf_closed Q)
    (Hstep : forall x : Chain (experiments.B_di gp ga),
               Q (elem x) -> Q (experiments.B_di gp ga (elem x))) :
    Q (tower.gfp (experiments.B_di gp ga)).
  Proof. apply (experiments.di_tower_gfp gp ga); assumption. Qed.

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

  (* The same certification by SECOND-ORDER TOWER INDUCTION
     ([experiments.f_below_w_tower]).  Here the obligations are discharged
     against a chain element [snd x] rather than against [sqr] itself, and the
     induction hypothesis [IH : sqr <= snd x] is what closes the gap.  This is
     the tower-native route to an active up-to technique: the target is a chain
     element, so anything known about chain elements is available. *)
  Theorem sqr_below_w_tower : sqr <= w.
  Proof.
    apply experiments.f_below_w_tower. intros x IH. split.
    - intros S1 S2 H t1 t2 [t3 [H1 H2]].
      (* one step into [g_p (sqr S2)], then the IH lifts it to [g_p (snd x S2)] *)
      apply (g_pF_mono (IH S2)).
      exact (g_pF_trans (H t1 t3 H1) (H t3 t2 H2)).
    - intros S1 S2 _ H t1 t2 [t3 [H1 H2]].
      apply (@g_aF_mono E R RR _ _ (IH S2)).
      exact (g_aF_trans (H t1 t3 H1) (H t3 t2 H2)).
  Qed.

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
(** ** WEAK bisimilarity: passive owns tau, active is the eutt functor.

    For eutt the two concerns are TAU (passive) and the observable behaviour
    (active).  So [c_p] owns the tau structure only -- synchronisation and
    stripping -- and is PERMISSIVE at both frontiers; in particular it does not
    check [RR].  The active functor is the full eutt functor, putting the Ret
    and Vis obligations on the active side, which is where up-to-eutt is valid
    (the Vis-Vis case).

    A discarded carve, recorded because the mistake is instructive: giving the
    passive half the [RR] check while ALSO giving it a stopping synchronised-tau
    rule makes it punish a eutt-closure for exposing a deferred Ret check -- an
    obligation that is not the tau concern at all.  It also forces a painful
    tau-alignment reconstruction to recover eutt.  With the carve below,
    [di_similarity] is eutt in a few lines. *)

Section weak.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).
  Notation Rel := (itree -> itree -> Prop).

  Inductive c_pF (sim : Rel) : itree' E R -> itree' E R -> Prop :=
  | CpRet r1 r2 : c_pF sim (RetF r1) (RetF r2)
  | CpVis {u1} (e1 : E u1) k1 {u2} (e2 : E u2) k2 : c_pF sim (VisF e1 k1) (VisF e2 k2)
  | CpTau m1 m2 (REL : sim m1 m2) : c_pF sim (TauF m1) (TauF m2)
  | CpTauL t1 ot2 (REL : c_pF sim (observe t1) ot2) : c_pF sim (TauF t1) ot2
  | CpTauR ot1 t2 (REL : c_pF sim ot1 (observe t2)) : c_pF sim ot1 (TauF t2).

  Lemma c_pF_mono {sim sim' : Rel} (H : sim <= sim') : c_pF sim <= c_pF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply CpRet.
    - apply CpVis.
    - apply CpTau; apply H; assumption.
    - apply CpTauL; assumption.
    - apply CpTauR; assumption.
  Qed.

  Definition c_p_ (sim : Rel) : Rel := fun t1 t2 => c_pF sim (observe t1) (observe t2).
  Lemma c_p__mono : Proper (leq ==> leq) c_p_.
  Proof. intros sim sim' H t1 t2 He. exact (c_pF_mono H _ _ He). Qed.
  Definition c_p : mon Rel := {| body := c_p_ ; Hbody := c_p__mono |}.

  Notation c_a := (@eqit_mon E R RR true true).
  #[local] Instance Pcp : Progress (progress_mon c_p) := progress_mono c_p.
  #[local] Instance Pca : Progress (progress_mon c_a) := progress_mono c_a.

  Notation compan := (diacritical_companion.compan (progress_mon c_p) (progress_mon c_a)).
  Notation u := (fst compan).
  Notation w := (snd compan).

  Lemma eutt_below_cp (sim : Rel) : eqitF RR true true sim <= c_pF sim.
  Proof.
    intros ot1 ot2 H. induction H.
    - apply CpRet.
    - apply CpTau; assumption.
    - apply CpVis.
    - apply CpTauL; assumption.
    - apply CpTauR; assumption.
  Qed.

  (* the meet is exactly eutt; both directions are easy, since the active half
     alone already pins the behaviour down *)
  Theorem disim_weak_eutt :
    di_similarity (progress_mon c_p) (progress_mon c_a) == eutt RR.
  Proof.
    apply antisym.
    - unfold di_similarity. apply sup_spec. intros S [_ Ha].
      unfold eutt, eqit. apply leq_gfp. exact Ha.
    - apply leq_xsup. split.
      + intros t1 t2 H. apply eutt_below_cp.
        exact (gfp_pfp (eqit_mon RR true true) t1 t2 H).
      + exact (gfp_pfp (eqit_mon RR true true)).
  Qed.

  (* the second-order tower, for eutt *)
  Corollary weak_compan_gfp : compan == tower.gfp (experiments.B_di c_p c_a).
  Proof. apply (experiments.compan_gfp c_p c_a). Qed.

  (* diacritical coinduction into eutt: progress passively via [u], actively
     via [w] *)
  Corollary eutt_di_coinduction (S : Rel)
    (Hp : S <= c_p (u S)) (Ha : S <= c_a (w S)) : S <= eutt RR.
  Proof.
    rewrite <- disim_weak_eutt.
    apply (diacritical_companion.soundness (progress_mon c_p) (progress_mon c_a)); assumption.
  Qed.

  (* [pev_weak] is unconditional, so [w] is itself c_p-compatible: the
     diacritical extra power is confined to the CONDITIONAL active law and can
     never exceed the passive companion.  Contrapositive: a technique unsound
     for the passive behaviour cannot be active-sound either. *)
  Corollary weak_w_below_passive : w <= companion.t c_p.
  Proof. exact (experiments.w_below_t1 c_p c_a). Qed.

  Corollary not_below_w (f : mon Rel) :
    ~ (f <= companion.t c_p) -> ~ (f <= w).
  Proof. intros Hn H. apply Hn. rewrite H. exact weak_w_below_passive. Qed.

  (* ---- payoff: tau is silent ---- *)
  Hypothesis Hrefl : forall r, RR r r.

  Definition tau_shift : Rel :=
    fun t1 t2 => t1 = t2 \/ observe t1 = TauF t2 \/ observe t2 = TauF t1.

  Lemma tau_shift_diag (ot : itree' E R) : eqitF RR true true tau_shift ot ot.
  Proof.
    destruct ot as [ r | m | X e k ].
    - apply EqRet, Hrefl.
    - apply EqTau. left. reflexivity.
    - apply EqVis. intro v. left. reflexivity.
  Qed.

  Lemma tau_shift_below_eutt : tau_shift <= eutt RR.
  Proof.
    unfold eutt, eqit. apply leq_gfp.
    intros t1 t2 [<- | [Ht | Ht]]; cbn; unfold eqit_.
    - apply tau_shift_diag.
    - rewrite Ht. apply EqTauL; [ reflexivity | apply tau_shift_diag ].
    - rewrite Ht. apply EqTauR; [ reflexivity | apply tau_shift_diag ].
  Qed.

  Theorem eutt_tau  (t : itree) : eutt RR (Tau t) t.
  Proof. apply tau_shift_below_eutt. right. left. reflexivity. Qed.
  Theorem eutt_tau' (t : itree) : eutt RR t (Tau t).
  Proof. apply tau_shift_below_eutt. right. right. reflexivity. Qed.
  Corollary eutt_refl (t : itree) : eutt RR t t.
  Proof. apply tau_shift_below_eutt. left. reflexivity. Qed.

  (* OPEN.  Whether up-to-eutt (the two-sided closure [eutt o S o eutt]) is
     [<= w] here is not settled.  The remaining obligation is [pev_weak], which
     is unconditional and quantifies over an ARBITRARY target [S]:
       [S1 <= c_p S2 -> eutt_clo S1 <= c_p (eutt_clo S2)].
     The case to examine is [CpTau] with an [S2] relating a divergent tree to a
     convergent one: the closure absorbs taus on one side only, and [c_pF],
     inductive in its stripping rules, may then have no derivation.  If the
     two-sided closure does fail, the question becomes which guarded form
     succeeds. *)

End weak.
