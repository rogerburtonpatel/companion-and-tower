From Stdlib Require Import Utf8.
Require Import lattice.
Require Import progress evolution diacritical_companion higherorder.

Section UpToImproved.
Context {X : Type} {CL : CompleteLattice X}.

Variable p : X → X → Prop.
Variable b : X → X → Prop.

Context {PP : Progress p} {PB : Progress b}.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (b R S) (at level 70).
Notation "f ↝ₚ g" := (p_evolution p f g) (at level 70).
Notation "f ↝ₐ g" := (a_evolution p b f g) (at level 70).

Notation u := (fst (compan p b)).
Notation w := (snd (compan p b)).

Notation U := (fst (compan (p_evolution p) (a_evolution p b))).
Notation W := (snd (compan (p_evolution p) (a_evolution p b))).

Notation "⊥" := (@lattice_bot [X ⇒ X] _).

Variables s f : [X ⇒ X].

Definition U_weak_better :=
  ∏ {h | f <= h ∧ U_weak p b (s, h) <= h ∧ h ° U_strong p b (s, ⊥) <= h}.

Lemma f_of_U_weak_better : f <= U_weak_better.
Proof. apply inf_spec; tauto. Qed.

Lemma U_weak_of_U_weak_better :
  U_weak p b (s, U_weak_better) <= U_weak_better.
Proof.
apply inf_spec; intros h [ H1 [ H2 H3 ] ].
etransitivity; [ | exact H2 ].
apply Hbody, Hbody. split; [ reflexivity | ].
apply leq_infx; auto.
Qed.

Lemma U_weak_better_comp_U_strong :
  U_weak_better ° U_strong p b (s, ⊥) <= U_weak_better.
Proof.
apply inf_spec; intros h [ H1 [ H2 H3 ] ].
etransitivity; [ | exact H3 ].
eapply comp_leq; [ | reflexivity ].
apply leq_infx; auto.
Qed.

Variable Hsp : s ↝[ p ]     U_strong p b (s, ⊥).
Variable Hfp : f ↝[ p ]     U_weak_better.
Variable Hsa : s ↝[ b ]     W_weak p b (s, f).
Variable Hfa : f ↝[ p # b ] W_weak p b (s, f).

Lemma U_strong_bot_cl_pas : U_strong p b (s, ⊥) ↝[p] U_strong p b (s, ⊥).
Proof.
assert (Hev : (s, ⊥) ↝ₚ U (s, ⊥)) by
  (split; [ assumption | apply progress_limit_l; tauto ]).
apply (ucompan_compatible (p_evolution p) (a_evolution p b)) in Hev.
rewrite (ucompan_idempotent' _ _) in Hev.
apply Hev.
Qed.

Lemma U_strong_bot_cl_act : U_strong p b (s, ⊥) ↝[p # b] W_weak p b (s, f).
Proof.
assert (Hev : (s, ⊥) ↝ₐ W (s, f)) by
  (split; [ eassumption | apply progress_limit_l; tauto ]).
apply (ucompan_compatible (p_evolution p) (a_evolution p b)) in Hev.
rewrite (wcompan_idempotent' _ _) in Hev.
eapply progress_monotone_l; [ apply (U_strong_U_weak _ _) | ].
apply Hev.
Qed.

Lemma U_weak_better_pas : U_weak_better ↝[p] U_weak_better.
Proof.
assert (Hind : (U_weak_better <= ∐ {h | h ↝[p] U_weak_better})).
{ apply leq_infx; split; [ | split ].
+ apply leq_xsup; assumption.
+ apply leq_xsup.
  assert (Hev_s : (s, ∐ {h | h ↝[p] U_weak_better}) ↝ₚ
    (U_strong p b (s, ⊥), U_weak_better)).
  { split; [ assumption | ].
    apply progress_limit_l; auto.
  }
  apply (ucompan_compatible (p_evolution p) (a_evolution p b)) in Hev_s.
  destruct Hev_s as [ _ Hev_s ].
  eapply progress_monotone_r; [ | apply Hev_s ].
  etransitivity; [ | apply U_weak_of_U_weak_better ].
  rewrite <- (U_weak_U _ _).
  apply (Hbody snd_mon).
  apply Hbody; split.
  - apply (Hbody fst_mon).
    apply Hbody; split; [ reflexivity | ].
    apply sup_spec; tauto.
  - apply (f_U_weak' _ _).
+ apply leq_xsup.
  eapply progress_monotone_r; [ apply U_weak_better_comp_U_strong | ].
  apply evolution_comp; [ | apply U_strong_bot_cl_pas ].
  apply progress_limit_l; auto.
}
eapply progress_monotone_l; [ apply Hind | ].
apply progress_limit_l; auto.
Qed.

Lemma U_weak_better_act : U_weak_better ↝[p # b] W_weak p b (s, f).
Proof.
assert (Hind : (U_weak_better <= ∐ {h | h ↝[p # b] W_weak p b (s, f)})).
{ apply leq_infx; split; [ | split ].
+ apply leq_xsup; assumption.
+ apply leq_xsup.
  assert (Hev_s : (s, ∐ {h | h ↝[p # b] W_weak p b (s, f)}) ↝ₐ W (s, f)).
  { split; [ assumption | ].
    apply progress_limit_l; auto.
  }
  apply (ucompan_compatible (p_evolution p) (a_evolution p b)) in Hev_s.
  rewrite (wcompan_idempotent' _ _) in Hev_s.
  apply Hev_s.
+ apply leq_xsup.
  rewrite <- (comp_W_weak _ _).
  apply r_evolution_comp;
    [ | apply U_strong_bot_cl_pas | apply U_strong_bot_cl_act ].
  apply progress_limit_l; auto.
}
eapply progress_monotone_l; [ apply Hind | ].
apply progress_limit_l; auto.
Qed.

Theorem make_upto_better : (s, f) <= compan p b.
Proof.
transitivity (s, U_weak_better);
  [ split; [ reflexivity | apply f_of_U_weak_better ] | ].
apply (make_upto _ _).
+ eapply progress_monotone_r; [ | eassumption ].
  apply (Hbody fst_mon), Hbody.
  split; [ reflexivity | apply sup_spec; tauto ].
+ eapply progress_monotone_r; [ | apply U_weak_better_pas ].
  apply (f_U_weak' _ _).
+ eapply progress_monotone_r; [ | eassumption ].
  apply (Hbody snd_mon), Hbody.
  split; [ reflexivity | apply f_of_U_weak_better ].
+ eapply progress_monotone_r; [ | apply U_weak_better_act ].
  apply (Hbody snd_mon), Hbody.
  split; [ reflexivity | apply f_of_U_weak_better ].
Qed.

End UpToImproved.