(** * Vis-guarded up-to-eutt: settling the OPEN note of [diacritical_tower_example]

    Everything is reused from [diacritical_tower_example]; nothing is copied. *)

Require Import lattice tower companion progress diacritical_companion.
Require Import diacritical_tower_example.

(* no [Set Implicit Arguments]: we want [no_ret_vis]'s relation argument explicit *)

(* ------------------------------------------------------------------ *)
(** ** A closed instance: one event of arity [unit], results in [nat]. *)

Definition Ev : Type -> Type := fun _ => unit.
Notation IT := (itree Ev nat).
Notation Rel := (IT -> IT -> Prop).

Definition kk : unit -> IT := fun _ => Ret 0.
Definition A : IT := Ret 0.
Definition B : IT := Vis tt kk.

(** the two relations of the counterexample *)
Definition S0 : Rel := fun t1 t2 => t1 = A /\ t2 = B.
Definition R0 : Rel := fun t1 t2 => t1 = Tau A /\ t2 = Tau B.

(** [c_pF] has no rule relating a [RetF] to a [VisF]: [c_p] is permissive
    WITHIN a frontier but still demands both heads be the same KIND. *)
Lemma no_ret_vis (X : Rel) : ~ c_pF X (observe A) (observe B).
Proof. intro H. inversion H. Qed.

(** the two-sided up-to-eutt closure *)
Program Definition eutt_clo : mon Rel :=
  {| body S := fun t1 t2 => exists a b, eutt eq t1 a /\ S a b /\ eutt eq b t2 |}.
Next Obligation.
  intros S1 S2 HS t1 t2 (a & b & H1 & H2 & H3).
  exists a, b. repeat split; auto. now apply HS.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Step 1(a): the passive law of [f_below_w] / [f_below_w_cup] fails. *)

Definition Hrefl_nat : forall r : nat, r = r := @eq_refl nat.

Lemma R0_le_cp_S0 : R0 <= c_p S0.
Proof. intros t1 t2 (-> & ->). apply CpTau. split; reflexivity. Qed.

(** the closure strips the very taus the [CpTau] step relied on *)
Lemma AB_in_eutt_clo_R0 : eutt_clo R0 A B.
Proof.
  exists (Tau A), (Tau B). repeat split.
  - apply eutt_tau'; exact Hrefl_nat.
  - apply eutt_tau; exact Hrefl_nat.
Qed.

Lemma passive_law_fails :
  ~ (forall S1 S2 : Rel, S1 <= c_p S2 -> eutt_clo S1 <= c_p (cup (eutt_clo S2) S2)).
Proof.
  intro H. apply (no_ret_vis (cup (eutt_clo S0) S0)).
  exact (H R0 S0 R0_le_cp_S0 A B AB_in_eutt_clo_R0).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Step 1(b): [eutt_clo <= w] is false outright. *)

(** [R0] progresses into the closure of itself... *)
Lemma R0_le_cp_clo_R0 : R0 <= c_p (eutt_clo R0).
Proof.
  intros t1 t2 (-> & ->). apply CpTau. exact AB_in_eutt_clo_R0.
Qed.

(** ...but is not below [gfp c_p], because [A] and [B] are not. *)
Lemma not_gfp_cp_AB : ~ gfp c_p A B.
Proof.
  intro H. apply (no_ret_vis (gfp c_p)). exact (gfp_pfp c_p A B H).
Qed.

(** stripping either tau exposes the same [RetF]-vs-[VisF] frontier *)
Lemma no_ret_tauB (X : Rel) : ~ c_pF X (observe A) (TauF B).
Proof. intro H. inversion H; subst. apply (no_ret_vis X). exact REL. Qed.

Lemma no_tauA_vis (X : Rel) : ~ c_pF X (TauF A) (observe B).
Proof. intro H. inversion H; subst. apply (no_ret_vis X). exact REL. Qed.

Lemma cpF_TauA_TauB_inv (X : Rel) : c_pF X (TauF A) (TauF B) -> X A B.
Proof.
  intro H. inversion H; subst.
  - assumption.
  - exfalso. apply (no_ret_tauB X). exact REL.
  - exfalso. apply (no_tauA_vis X). exact REL.
Qed.

Lemma not_R0_le_gfp_cp : ~ R0 <= gfp c_p.
Proof.
  intro H. apply not_gfp_cp_AB.
  assert (HT : gfp c_p (Tau A) (Tau B)) by (apply H; split; reflexivity).
  apply (gfp_pfp c_p) in HT. exact (cpF_TauA_TauB_inv _ HT).
Qed.

(** so up-to-eutt is not sound for the PASSIVE behaviour ... *)
Theorem eutt_clo_not_below_t_cp : ~ eutt_clo <= companion.t c_p.
Proof.
  intro Hle. apply not_R0_le_gfp_cp.
  apply companion.coinduction.
  transitivity (c_p (eutt_clo R0)).
  - exact R0_le_cp_clo_R0.
  - exact (Hbody c_p _ _ (Hle R0)).
Qed.

(** ... and therefore not below the ACTIVE companion either. *)
Theorem eutt_clo_not_below_w : ~ eutt_clo <= snd (compan (progress_mon c_p)
                                        (progress_mon (eqit_mon (@eq nat) true true))).
Proof. exact (not_below_w (@eq nat) eutt_clo eutt_clo_not_below_t_cp). Qed.

(* ================================================================== *)
(** * Step 2: can [ptower]'s accumulated/goal split carry the Vis guard? *)

Notation bb := (eqit_mon (@eq nat) true true).

(** the guarded premise: every [S]-pair is a Vis-match whose continuations
    lie in [eutt_clo S] or in [S] itself. *)
Definition vis_guarded (S : Rel) : Prop :=
  forall t1 t2, S t1 t2 ->
    exists (u : Type) (e : Ev u) (k1 k2 : u -> IT),
      observe t1 = VisF e k1 /\ observe t2 = VisF e k2 /\
      forall v, cup (eutt_clo S) S (k1 v) (k2 v).

(** ** 2.1 the [ptower] STEP goal discharges -- this is what design C lacked *)
Lemma spike_step (S : Rel) (Hg : vis_guarded S) (x : Chain bb) :
  eutt_clo S <= elem x -> S <= elem x -> S <= bb (elem x).
Proof.
  intros HQ HP t1 t2 Ht.
  destruct (Hg t1 t2 Ht) as (u & e & k1 & k2 & E1 & E2 & Hk).
  cbn. unfold eqit_. rewrite E1, E2.
  apply EqVis. intro v.
  destruct (Hk v) as [Hc | Hs].
  - exact (HQ _ _ Hc).
  - exact (HP _ _ Hs).
Qed.

(** ** 2.2 but the CONCLUSION is circular.

    [ptower] yields [forall x : Chain, Q x -> P x].  Instantiating at
    [chain_gfp] demands [Q (gfp bb)], i.e. [eutt_clo S <= eutt] -- which already
    gives the goal [S <= eutt].  So the conclusion cannot be discharged. *)

Lemma S_le_eutt_clo (S : Rel) : S <= eutt_clo S.
Proof.
  intros t1 t2 Ht. exists t1, t2. repeat split; try assumption;
  apply eutt_refl; exact Hrefl_nat.
Qed.

Lemma Q_at_gfp_implies_goal (S : Rel) : eutt_clo S <= eutt eq -> S <= eutt eq.
Proof. intro HQ. rewrite <- HQ. apply S_le_eutt_clo. Qed.

(** ** 2.3 and the obvious repair is not [Proper].

    Taking [Q x := eutt_clo x <= x] ("x is eutt-closed") is a DOWN-closed
    condition, while [ptower] demands an UP-closed one.  Same obstruction as
    [diacritical_redesign.v] records for the post-fixpoint premise. *)

Lemma Tau_A_neq_A : Tau A <> A.
Proof.
  intro H. assert (observe (Tau A) = observe A) as HO by (rewrite H; reflexivity).
  cbn in HO. discriminate.
Qed.

Lemma TauA_B_in_eutt_clo_S0 : eutt_clo S0 (Tau A) B.
Proof.
  exists A, B. repeat split.
  - apply eutt_tau; exact Hrefl_nat.
  - apply eutt_refl; exact Hrefl_nat.
Qed.

Lemma S0_not_eutt_closed : ~ eutt_clo S0 <= S0.
Proof.
  intro H. destruct (H (Tau A) B TauA_B_in_eutt_clo_S0) as [HA _].
  exact (Tau_A_neq_A HA).
Qed.

Lemma bot_eutt_closed : eutt_clo (bot : Rel) <= (bot : Rel).
Proof. intros t1 t2 (a & b & _ & [] & _). Qed.

Theorem eutt_closedness_not_monotone :
  ~ Proper (leq ==> leq) (fun x : Rel => eutt_clo x <= x).
Proof.
  intro HP. apply S0_not_eutt_closed.
  apply (HP (bot : Rel) S0).
  - apply leq_bx.
  - exact bot_eutt_closed.
Qed.

(* ================================================================== *)
(** * Step 2. Carrying the guard inside the functor.

    [eqitF2] splits the relation argument of [eqitF] in two.  One argument
    serves the Tau rule and the other serves the Vis rule.  Setting the Vis
    argument to the up-to-eutt closure is what records the bit. *)

Section vis_guard.
  Context {E : Type -> Type} {Res : Type} (RR : Res -> Res -> Prop).
  Notation T := (itree E Res).
  Notation Relr := (T -> T -> Prop).

  Program Definition eclo : mon Relr :=
    {| body S := fun t1 t2 => exists a c, eutt RR t1 a /\ S a c /\ eutt RR c t2 |}.
  Next Obligation.
    intros S1 S2 HS t1 t2 (a & c & H1 & H2 & H3).
    exists a, c. repeat split; auto. now apply HS.
  Qed.

  Inductive eqitF2 (simTau simVis : Relr) : itree' E Res -> itree' E Res -> Prop :=
  | E2Ret r1 r2 (REL : RR r1 r2) : eqitF2 simTau simVis (RetF r1) (RetF r2)
  | E2Tau m1 m2 (REL : simTau m1 m2) : eqitF2 simTau simVis (TauF m1) (TauF m2)
  | E2Vis {u} (e : E u) k1 k2 (REL : forall v, simVis (k1 v) (k2 v)) :
      eqitF2 simTau simVis (VisF e k1) (VisF e k2)
  | E2TauL t1 ot2 (REL : eqitF2 simTau simVis (observe t1) ot2) :
      eqitF2 simTau simVis (TauF t1) ot2
  | E2TauR ot1 t2 (REL : eqitF2 simTau simVis ot1 (observe t2)) :
      eqitF2 simTau simVis ot1 (TauF t2).

  (** Obligation 1: monotone in both arguments. *)
  Lemma eqitF2_mono {sT sT' sV sV' : Relr}
    (HT : sT <= sT') (HV : sV <= sV') : eqitF2 sT sV <= eqitF2 sT' sV'.
  Proof.
    intros ot1 ot2 H. induction H.
    - apply E2Ret; assumption.
    - apply E2Tau; now apply HT.
    - apply E2Vis; intro v; now apply HV.
    - apply E2TauL; assumption.
    - apply E2TauR; assumption.
  Qed.

  (** Obligation 2: [b2] is a monotone function on the same lattice. *)
  Definition b2_ (S : Relr) : Relr :=
    fun t1 t2 => eqitF2 S (eclo S) (observe t1) (observe t2).

  Lemma b2__mono : Proper (leq ==> leq) b2_.
  Proof.
    intros S1 S2 HS t1 t2 H.
    exact (eqitF2_mono HS (Hbody eclo _ _ HS) _ _ H).
  Qed.

  Definition b2 : mon Relr := {| body := b2_ ; Hbody := b2__mono |}.

  (** Obligation 3: [b <= b2], hence [gfp b <= gfp b2]. *)
  Hypothesis Hrefl : forall r : Res, RR r r.

  Lemma S_le_eclo (S : Relr) : S <= eclo S.
  Proof.
    intros t1 t2 H. exists t1, t2. repeat split; try assumption;
    apply eutt_refl; exact Hrefl.
  Qed.

  Lemma b_le_b2 : eqit_mon RR true true <= b2.
  Proof.
    intros S t1 t2 H. cbn in H. unfold eqit_ in H. cbn. unfold b2_.
    induction H.
    - apply E2Ret; assumption.
    - apply E2Tau; assumption.
    - apply E2Vis; intro v. apply S_le_eclo. apply REL.
    - apply E2TauL; assumption.
    - apply E2TauR; assumption.
  Qed.

  Corollary gfp_b_le_gfp_b2 : gfp (eqit_mon RR true true) <= gfp b2.
  Proof. apply gfp_leq, b_le_b2. Qed.

End vis_guard.
