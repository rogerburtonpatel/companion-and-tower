(** * Sandbox: minimal itrees + [eqit], stripped to just the definitions.

    Copied and pared down from InteractionTrees ([Core/ITreeDefinition.v] and the
    first part of [Eq/Eqit.v]) -- everything not needed to *state* [eqit] is
    removed (no [bind], [iter], notations scopes, ExtLib, etc.).

    Two deviations from upstream, both to keep the sandbox small:
    - phrased over THIS coinduction library ([mon]/[gfp] from [lattice]/[companion]);
    - homogeneous: we fix the event type [E], result type [R], and relation [RR],
      so the carrier lattice is the plain relation lattice
      [itree E R -> itree E R -> Prop] rather than the heterogeneous
      [forall R1 R2, (R1 -> R2 -> Prop) -> ...].  This is the lattice on which we
      want to hang the diacritical companion. *)

From Stdlib Require Import Utf8 Setoid Morphisms Program.Equality.
Require Import lattice progress evolution companion diacritical_companion tower.
Require Import tactics utils.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

(* ------------------------------------------------------------------------- *)
(** ** Interaction trees (from [ITreeDefinition.v], minimal) *)

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

(* The [itree] constructors have baked in their implicit type parameter above;
   turn implicits back off so ordinary lemma binders (e.g. [b1 b2]) stay
   explicit. *)
Unset Contextual Implicit.
Unset Implicit Arguments.

(* ------------------------------------------------------------------------- *)
(** ** [eqit] (from [Eqit.v], minimal, homogeneous)

    [b1]/[b2] toggle whether taus may be stripped on the left/right.
    - [eqit false false] = strong bisimilarity ([eq_itree]);
    - [eqit true  true ] = weak bisimilarity up to tau ([eutt]). *)

Local Coercion is_true : bool >-> Sortclass.

Section eqit.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Inductive eqitF (b1 b2 : bool) (sim : itree -> itree -> Prop) :
    itree' E R -> itree' E R -> Prop :=
  | EqRet r1 r2
      (REL : RR r1 r2) :
      eqitF b1 b2 sim (RetF r1) (RetF r2)
  | EqTau m1 m2
      (REL : sim m1 m2) :
      eqitF b1 b2 sim (TauF m1) (TauF m2)
  | EqVis {u} (e : E u) k1 k2
      (REL : forall v, sim (k1 v) (k2 v)) :
      eqitF b1 b2 sim (VisF e k1) (VisF e k2)
  | EqTauL t1 ot2
      (CHECK : b1)
      (REL : eqitF b1 b2 sim (observe t1) ot2) :
      eqitF b1 b2 sim (TauF t1) ot2
  | EqTauR ot1 t2
      (CHECK : b2)
      (REL : eqitF b1 b2 sim ot1 (observe t2)) :
      eqitF b1 b2 sim ot1 (TauF t2).

  (* Compose the [itreeF]-level transformer with [observe]. *)
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
(** ** Attempt: split eutt's functor as a permissive MEET [f_p ⊓ f_a].

    Concern split (silent vs observable):
    - [f_p] (passive) owns the τ structure -- synchronised taus [PTau] and
      tau-stripping [PTauL]/[PTauR] -- and is *permissive* on the observable
      payload: [PRet] relates ANY two [Ret]s (no [RR]) and [PVis] relates ANY
      two [Vis]es (events not even matched).
    - [f_a] (active) owns the observable payload -- [ARet] checks [RR], [AVis]
      checks the continuations -- and is *permissive* on τ: any τ-headed pair is
      related ([ATauL]/[ATauR]).

    If [f_p ⊓ f_a] equalled [eqit_ true true] we could [b := cap f_p f_a] and get
    eutt (and the whole diacritical stack) for free.  It does NOT -- see the
    counterexample in [meet_over_approximates] below. *)

Section split.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Inductive f_pF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | PRet r1 r2 : f_pF sim (RetF r1) (RetF r2)
  | PVis u1 (e1 : E u1) k1 u2 (e2 : E u2) k2 : f_pF sim (VisF e1 k1) (VisF e2 k2)
  | PTau m1 m2 (REL : sim m1 m2) : f_pF sim (TauF m1) (TauF m2)
  | PTauL t1 ot2 (REL : f_pF sim (observe t1) ot2) : f_pF sim (TauF t1) ot2
  | PTauR ot1 t2 (REL : f_pF sim ot1 (observe t2)) : f_pF sim ot1 (TauF t2).

  Inductive f_aF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | ARet r1 r2 (REL : RR r1 r2) : f_aF sim (RetF r1) (RetF r2)
  | AVis {u} (e : E u) k1 k2 (REL : forall v, sim (k1 v) (k2 v)) : f_aF sim (VisF e k1) (VisF e k2)
  | ATauL m1 ot2 : f_aF sim (TauF m1) ot2
  | ATauR ot1 m2 : f_aF sim ot1 (TauF m2).

  Lemma f_pF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : f_pF sim <= f_pF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply PRet.
    - apply PVis.
    - apply PTau; apply H; assumption.
    - apply PTauL; assumption.
    - apply PTauR; assumption.
  Qed.

  Lemma f_aF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : f_aF sim <= f_aF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply ARet; assumption.
    - apply AVis; intro v; apply H; apply REL.
    - apply ATauL.
    - apply ATauR.
  Qed.

  Definition f_p_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => f_pF sim (observe t1) (observe t2).
  Definition f_a_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => f_aF sim (observe t1) (observe t2).

  Lemma f_p__mono : Proper (leq ==> leq) f_p_.
  Proof. intros sim sim' H t1 t2 He. exact (f_pF_mono H _ _ He). Qed.
  Lemma f_a__mono : Proper (leq ==> leq) f_a_.
  Proof. intros sim sim' H t1 t2 He. exact (f_aF_mono H _ _ He). Qed.

  Definition f_p : mon (itree -> itree -> Prop) := {| body := f_p_ ; Hbody := f_p__mono |}.
  Definition f_a : mon (itree -> itree -> Prop) := {| body := f_a_ ; Hbody := f_a__mono |}.

  (* The would-be combined behaviour.  By [di_similarity_meet_gfp],
     [di_similarity (progress_mon f_p) (progress_mon f_a) == gfp b_split];
     the question is whether [gfp b_split] is eutt.  It is not. *)
  Definition b_split : mon (itree -> itree -> Prop) := cap f_p f_a.

  (** Counterexample (why the τ-stripping meet over-approximates).

      Take [t1 := Tau (Ret a)], [t2 := Ret b] with [~ RR a b].  Then:

        eqit_ true true sim t1 t2
          = eqitF .. (TauF (Ret a)) (RetF b)
          = (strip left τ, EqTauL) eqitF .. (RetF a) (RetF b)
          = RR a b                                    = FALSE.

      But the meet [b_split sim t1 t2 = f_pF .. ∧ f_aF ..] is:

        f_pF sim (TauF (Ret a)) (RetF b)
          = (PTauL) f_pF sim (RetF a) (RetF b) = (PRet) TRUE   (RR not checked)
        f_aF sim (TauF (Ret a)) (RetF b)
          = (ATauL, τ on the left) TRUE                        (payload not reached)

      so [b_split sim t1 t2 = TRUE ≠ FALSE].  The [RR a b] obligation lives at
      the *stripped* frontier [(RetF a, RetF b)]; [f_a] is permissive as soon as
      it sees the leading τ and never reaches it, while [f_p] reaches it but is
      permissive there by design.  Neither factor checks it, so the meet relates
      [Tau (Ret a)] and [Ret b] even when [a ≠ b].

      Hence [gfp b_split ⊋ eutt]: the "define b from the split" route gives the
      WRONG gfp for eutt.  Strong bisim ([eq_itree], no [TauL]/[TauR]) has no
      stripping and splits cleanly; eutt does not. *)

End split.

(* ------------------------------------------------------------------------- *)
(** ** Strong bisimulation DOES split as a clean meet.

    For [eq_itree] ([b1=b2=false]) there is no τ-stripping, so the concern split
    works: [g_p] constrains τ (Tau/Tau), permissive on observables; [g_a]
    constrains observables (Ret via [RR], Vis via continuations), permissive on
    τ.  Their meet is *exactly* [eqit_ false false], so the diacritical companion
    of [(progress_mon g_p, progress_mon g_a)] recovers [eq_itree] -- the whole
    [di_similarity] stack, on real itrees. *)

Section split_strong.
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

  (* The meet is pointwise exactly the strong-bisim functor. *)
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

  (* Payoff: the diacritical di-similarity of the passive/active split is
     strong bisimilarity. *)
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

  (** Why CONJUNCTION (meet), not DISJUNCTION (join).

     Each functor is permissive on the *other* concern: [g_p] accepts any Ret/Vis
     pair (payload unchecked), [g_a] accepts any Tau pair.  The MEET reinstates
     both real conditions; the JOIN -- a union of two over-approximations -- holds
     unconditionally, i.e. relates any matching-head pair regardless of payload. *)

  (* meet recovers the real requirements: RR at Ret, [sim] at Tau. *)
  Example conjunction_ret sim r1 r2 : (cap g_p g_a) sim (Ret r1) (Ret r2) <-> RR r1 r2.
  Proof. split.
    - intros [_ Ha]. inversion Ha; subst; assumption.
    - intro. split; [ apply GpRet | apply GaRet; assumption ]. Qed.

  Example conjunction_tau sim m1 m2 : (cap g_p g_a) sim (Tau m1) (Tau m2) <-> sim m1 m2.
  Proof. split.
    - intros [Hp _]. inversion Hp; subst; assumption.
    - intro. split; [ apply GpTau; assumption | apply GaTau ]. Qed.

  (* join drops them: both hold with NO condition on the payload (unsound). *)
  Example disjunction_ret sim r1 r2 : (cup g_p g_a) sim (Ret r1) (Ret r2).
  Proof. left. apply GpRet. Qed.

  Example disjunction_tau sim m1 m2 : (cup g_p g_a) sim (Tau m1) (Tau m2).
  Proof. right. apply GaTau. Qed.

End split_strong.

(* ------------------------------------------------------------------------- *)
(** ** The dual: a genuine CASE-SPLIT of [eqitF] (no permissive cases).

    [h_p] gets only the τ clause, [h_a] only the observable clauses.  Now the
    JOIN reconstructs the behaviour ([h_p ⊔ h_a = eqit_ false false], so its gfp
    is [eq_itree]) -- the disjunction is correct here.  But the diacritical
    companion combines by MEET, and the meet of disjoint case-halves is EMPTY,
    so [di_similarity] of these two collapses to [bot].  Case-split + join and
    permissive + meet are dual; only the latter plugs into [di_similarity]. *)

Section split_cases.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation itree := (itree E R).

  Inductive h_pF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | HpTau m1 m2 (REL : sim m1 m2) : h_pF sim (TauF m1) (TauF m2).

  Inductive h_aF (sim : itree -> itree -> Prop) : itree' E R -> itree' E R -> Prop :=
  | HaRet r1 r2 (REL : RR r1 r2) : h_aF sim (RetF r1) (RetF r2)
  | HaVis {u} (e : E u) k1 k2 (REL : forall v, sim (k1 v) (k2 v)) : h_aF sim (VisF e k1) (VisF e k2).

  Lemma h_pF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : h_pF sim <= h_pF sim'.
  Proof. intros ot1 ot2 He. induction He. apply HpTau; apply H; assumption. Qed.
  Lemma h_aF_mono {sim sim' : itree -> itree -> Prop} (H : sim <= sim') : h_aF sim <= h_aF sim'.
  Proof.
    intros ot1 ot2 He. induction He.
    - apply HaRet; assumption.
    - apply HaVis; intro v; apply H; apply REL.
  Qed.

  Definition h_p_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => h_pF sim (observe t1) (observe t2).
  Definition h_a_ (sim : itree -> itree -> Prop) : itree -> itree -> Prop :=
    fun t1 t2 => h_aF sim (observe t1) (observe t2).
  Lemma h_p__mono : Proper (leq ==> leq) h_p_.
  Proof. intros sim sim' H t1 t2 He. exact (h_pF_mono H _ _ He). Qed.
  Lemma h_a__mono : Proper (leq ==> leq) h_a_.
  Proof. intros sim sim' H t1 t2 He. exact (h_aF_mono H _ _ He). Qed.
  Definition h_p : mon (itree -> itree -> Prop) := {| body := h_p_ ; Hbody := h_p__mono |}.
  Definition h_a : mon (itree -> itree -> Prop) := {| body := h_a_ ; Hbody := h_a__mono |}.
  #[local] Instance Php : Progress (progress_mon h_p) := progress_mono h_p.
  #[local] Instance Pha : Progress (progress_mon h_a) := progress_mono h_a.

  (* the JOIN of the two case-halves is exactly the strong-bisim functor *)
  Lemma join_eqitF sim ot1 ot2 :
    (h_pF sim ot1 ot2 \/ h_aF sim ot1 ot2) <-> eqitF RR false false sim ot1 ot2.
  Proof.
    split.
    - intros [Hp | Ha].
      + destruct Hp. apply EqTau; assumption.
      + destruct Ha; [ apply EqRet | apply EqVis ]; assumption.
    - intro H. induction H.
      + right; apply HaRet; assumption.
      + left;  apply HpTau; assumption.
      + right; apply HaVis; assumption.
      + discriminate CHECK.
      + discriminate CHECK.
  Qed.

  Lemma join_cases : cup h_p h_a == eqit_mon RR false false.
  Proof.
    apply antisym; intros sim t1 t2 H.
    - exact (proj1 (join_eqitF _ (observe t1) (observe t2)) H).
    - exact (proj2 (join_eqitF _ (observe t1) (observe t2)) H).
  Qed.

  (* so the JOIN reconstructs strong bisimilarity -- disjunction is fine HERE *)
  Corollary gfp_join_cases : gfp (cup h_p h_a) == eq_itree RR.
  Proof.
    unfold eq_itree, eqit. apply antisym; apply gfp_leq; rewrite join_cases; reflexivity.
  Qed.

  (* but the MEET of disjoint case-halves is empty: no pair is both τ and Ret/Vis *)
  Lemma meet_cases_empty : cap h_p h_a == bot.
  Proof.
    apply antisym; [ | apply leq_bx ].
    intros sim t1 t2 [Hp Ha]. inversion Hp; inversion Ha; congruence.
  Qed.

  (* hence the diacritical companion of these two collapses to bot -- useless *)
  Corollary di_similarity_cases_bot :
    di_similarity (progress_mon h_p) (progress_mon h_a) == bot.
  Proof.
    apply antisym; [ | apply leq_bx ].
    unfold di_similarity. apply sup_spec. intros S [H1 H2] t1 t2 HS.
    pose proof (H1 t1 t2 HS) as Hp. pose proof (H2 t1 t2 HS) as Ha.
    inversion Hp; inversion Ha; congruence.
  Qed.

End split_cases.

(* ------------------------------------------------------------------------- *)
(** ** The paper's fix for eutt: each half strips τ ITSELF.

    The earlier [f_p]/[f_a] failed because [f_a] was permissive on a *top-level* τ
    (no stripping), so it never reached the observable.  The paper's progresses
    instead do their own reduction ([→∗]) and are permissive only at the
    *frontier*, on the OTHER observable.  Here:
    - [b_p] (Ret concern): strips τ ([BpTauL]/[BpTauR]), checks [RR] at a Ret
      frontier ([BpRet]), and is permissive at a Vis frontier ([BpVis]);
    - [b_a] (Vis concern): strips τ, checks continuations at a Vis frontier
      ([BaVis]), permissive at a Ret frontier ([BaRet]).
    Both handle synchronised τ ([BpTau]/[BaTau]) identically.

    This fixes the over-approximation: the [Tau (Ret a)] vs [Ret b] pair is now
    correctly rejected ([meet_rejects]), because [b_p] strips AND checks [RR]. *)

Section split_weak.
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

  (* eutt-bisimulations refine BOTH halves (each clause maps across; the
     off-concern observable is dropped by the permissive constructor). *)
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

  (* the fix: strip-AND-check rejects the pair that [f_p]/[f_a] wrongly accepted *)
  Example meet_rejects sim a b (Hab : ~ RR a b) :
    ~ b_pF sim (observe (Tau (Ret a))) (observe (Ret b)).
  Proof. intro H. inversion H; subst. inversion REL; subst. contradiction. Qed.

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

  (* POSITIVE direction: eutt sits below the diacritical similarity of the split. *)
  Lemma eutt_below_meet : eqit_mon RR true true <= cap b_p b_a.
  Proof.
    intros sim t1 t2 H. split.
    - exact (eutt_below_bp sim _ _ H).
    - exact (eutt_below_ba sim _ _ H).
  Qed.

  Corollary eutt_below_gfp_meet : eutt RR <= gfp (cap b_p b_a).
  Proof. unfold eutt, eqit. apply gfp_leq. exact eutt_below_meet. Qed.

  (* [eutt] is itself a diacritical bisimulation (positive direction, pointwise):
     unfold [eutt] once ([gfp_pfp]) and feed each half. *)
  Lemma eutt_leq_disim : eutt RR <= di_similarity (progress_mon b_p) (progress_mon b_a).
  Proof.
    apply leq_xsup. split; intros t1 t2 H.
    - apply eutt_below_bp. exact (gfp_pfp (eqit_mon RR true true) t1 t2 H).
    - apply eutt_below_ba. exact (gfp_pfp (eqit_mon RR true true) t1 t2 H).
  Qed.

  (* The reconstruction lemma at the heart of soundness: the meet of the two
     halves refines eutt's functor.  Clean in every case EXCEPT where [b_p] and
     [b_a] strip τ on OPPOSITE sides -- there neither derivation gives the other
     what it needs (the naive τ-τ obstruction), and the honest fix is a
     well-founded induction on strip count (the τ-closure lemmas ITree proves for
     eutt).  Those two cross cases are the only [admit]s. *)
  Lemma meet_functor sim ot1 ot2 (Hp : b_pF sim ot1 ot2) :
    b_aF sim ot1 ot2 -> eqitF RR true true sim ot1 ot2.
  Proof.
    induction Hp as
      [ r1 r2 HRR | v1 ve1 vk1 v2 ve2 vk2 | m1 m2 Hsim | s1 os2 Hp' IH | os1 s2 Hp' IH ];
      intros Hba.
    - apply EqRet; assumption.
    - dependent destruction Hba. apply EqVis; assumption.
    - apply EqTau; assumption.
    - (* [BpTauL]: left is [TauF s1] *)
      inversion Hba; subst.
      + apply EqTau; assumption.                                (* BaTau: synchronised τ *)
      + apply EqTauL; [ reflexivity | apply IH; assumption ].   (* BaTauL: both strip left *)
      + admit.                                                  (* BaTauR: OPPOSITE strip *)
    - (* [BpTauR]: right is [TauF s2] *)
      inversion Hba; subst.
      + apply EqTau; assumption.                                (* BaTau *)
      + admit.                                                  (* BaTauL: OPPOSITE strip *)
      + apply EqTauR; [ reflexivity | apply IH; assumption ].   (* BaTauR: both strip right *)
  Admitted.

  (* SOUNDNESS: every diacritical bisimulation is a eutt-bisimulation.  The
     statement IS true (this is eutt soundness of the split); modulo the two
     cross cases in [meet_functor], the whole proof is by coinduction ([leq_gfp]):
     [di_similarity] is a post-fixpoint of eutt's functor.  The witness [sim] is
     below [di_similarity] (it lies in the sup), lifting the leaves; [meet_functor]
     does the structural work. *)
  Lemma disim_leq_eutt : di_similarity (progress_mon b_p) (progress_mon b_a) <= eutt RR.
  Proof.
    unfold eutt, eqit. apply leq_gfp. intros t1 t2 Hds.
    destruct Hds as [sim [Hbp Hba] H].
    assert (Hsub : sim <= di_similarity (progress_mon b_p) (progress_mon b_a))
      by (apply leq_xsup; split; assumption).
    apply (eqitF_mono RR true true Hsub).
    apply meet_functor.
    - exact (Hbp t1 t2 H).
    - exact (Hba t1 t2 H).
  Qed.

End split_weak.