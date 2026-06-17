From Stdlib Require Import Utf8.
Require Import lattice. 
Require Import progress evolution diacritical_companion.

Section HigherOrder.
Context {X : Type} {CLX : CompleteLattice X}.

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

Definition U_strong sf := fst_mon (U sf).
Definition U_weak   sf := snd_mon (U sf).
Definition W_strong sf := fst_mon (W sf).
Definition W_weak   sf := snd_mon (W sf).

Theorem make_upto s f :
  s ↝[ p ]   U_strong (s, f) →
  f ↝[ p ]     U_weak (s, f) →
  s ↝[ b ]     W_weak (s, f) →
  f ↝[ p # b ] W_weak (s, f) →
    (s, f) <= compan p b.
Proof.
intros; apply (soundness _ _); split; assumption.
Qed.

(* ========================================================================= *)
(* Duplications *)

Lemma D_s_monotone (sf sf' : L_lift X) : sf <= sf' →
  (fst sf ° fst sf, fst sf ° snd sf) <= (fst sf' ° fst sf', fst sf' ° snd sf').
Proof.
destruct sf as [ s f ]; destruct sf' as [ s' f' ].
intros [ Hs Hf ]; unfold fst, snd in Hs, Hf; split; unfold fst, snd.
+ rewrite Hs; reflexivity.
+ rewrite Hs, Hf; reflexivity.
Qed.

Lemma D_w_monotone (sf sf' : L_lift X) : sf <= sf' →
(fst sf ° fst sf, snd sf ° snd sf) <= (fst sf' ° fst sf', snd sf' ° snd sf').
Proof.
destruct sf as [ s f ]; destruct sf' as [ s' f' ].
intros [ Hs Hf ]; unfold fst, snd in Hs, Hf; split; unfold fst, snd.
+ rewrite Hs; reflexivity.
+ rewrite Hf; reflexivity.
Qed.

Definition D_s : [L_lift X ⇒ L_lift X] :=
  {| body    := λ sf, (fst sf ° fst sf, fst sf ° snd sf)
  ;  Hbody := D_s_monotone
  |}.

Definition D_w : [L_lift X ⇒ L_lift X] :=
  {| body    := λ sf, (fst sf ° fst sf, snd sf ° snd sf)
  ;  Hbody := D_w_monotone
  |}.

Lemma D_compatible :
  compatible (p_evolution p) (a_evolution p b) (D_s, D_w).
Proof.
split; split; split; intros [ s f ] [ s' f' ].
+ intro Hp; split; simpl.
  - apply evolution_comp; apply Hp.
  - apply evolution_comp; apply Hp.
+ intro Hp; split; simpl.
  - apply evolution_comp; apply Hp.
  - apply evolution_comp; apply Hp.
+ intro Hp; split; simpl.
  - apply evolution_comp; apply Hp.
  - split; intros; apply Hp, Hp; assumption.
+ intros Hp Ha; split.
  - simpl; split; intros; apply Ha, Ha; assumption.
  - apply r_evolution_comp; apply Hp || apply Ha.
Qed.

Lemma D_below_compan : (D_s, D_w) <= compan (p_evolution p) (a_evolution p b).
Proof. apply compat_below_compan, D_compatible. Qed.

Lemma D_s_below_U : D_s <= U.
Proof. apply D_below_compan. Qed.

Lemma D_w_below_W : D_w <= W.
Proof. apply D_below_compan. Qed.

(* ========================================================================= *)
(* Composition with w in passive case *)
(* In the old theory that things were not possible! *)

Lemma Cw_monotone (sf sf' : L_lift X) : sf <= sf' →
  (@lattice_bot [X ⇒ X] _, snd sf ° w) <= (lattice_bot, snd sf' ° w).
Proof.
destruct sf as [ s f ]; destruct sf' as [ s' f' ].
intros [ Hs Hf ]; unfold fst, snd in Hs, Hf; split; unfold fst, snd.
+ reflexivity.
+ rewrite Hf; reflexivity.
Qed.

Definition Cw : [L_lift X ⇒ L_lift X] :=
  {| body    := λ sf, (lattice_bot, snd sf ° w)
  ;  Hbody   := Cw_monotone
  |}.

Lemma Cw_compatible :
  compatible (p_evolution p) (a_evolution p b) (Cw, Cw).
Proof.
split; split; split; intros [ s f ] [ s' f' ]; unfold fst, snd.
+ intro Hp; split.  
  - apply progress_limit_l; tauto. 
  - apply evolution_comp; [ apply Hp | apply (wcompan_compatible _ _) ].
+ intro Hp; split.
  - apply progress_limit_l; tauto.
  - apply evolution_comp; [ apply Hp | apply (wcompan_compatible _ _) ].
+ intro Hp; split.
  - apply progress_limit_l; tauto.
  - apply r_evolution_comp.
    * apply Hp.
    * apply (wcompan_compatible _ _).
    * apply (wcompan_compatible _ _).
+ intros Hp Ha; split.
  - apply progress_limit_l; tauto.
  - split; intros R S HR HRS.
    apply Ha; apply (wcompan_compatible _ _); assumption.
Qed.

Lemma Cw_below_compan :
  (Cw, Cw) <= compan (p_evolution p) (a_evolution p b).
Proof. apply compat_below_compan, Cw_compatible. Qed.

Lemma Cw_below_U : Cw <= U.
Proof. apply Cw_below_compan. Qed.

(* ========================================================================= *)
(* Properties of U_strong *)

Lemma s_U_strong sf : fst sf <= U_strong sf.
Proof.
assert (H : sf <= U sf) by apply (id_below_ucompan _ _).
apply H.
Qed.

Lemma u_U_strong sf : u <= U_strong sf.
Proof.
assert (H : compan p b <= U sf) by apply (disim_const_below_ucompan _ _).
apply H.
Qed.

Lemma id_U_strong sf : id <= U_strong sf.
Proof.
etransitivity; [ apply (id_below_ucompan p b) | apply u_U_strong ].
Qed.

Lemma U_strong_U sf : U_strong (U sf) <= U_strong sf.
Proof.
unfold U_strong; rewrite (ucompan_idempotent' _ _); reflexivity.
Qed.

Lemma comp_U_strong sf : U_strong sf ° U_strong sf <= U_strong sf.
Proof.
change (fst_mon (D_s (U sf)) <= U_strong sf).
rewrite D_s_below_U, (ucompan_idempotent' _ _); reflexivity.
Qed.

(* ========================================================================= *)
(* Properties of U_weak *)

Lemma f_U_weak sf : snd sf <= U_weak sf.
Proof.
assert (H : sf <= U sf) by apply (id_below_ucompan _ _).
apply H.
Qed.

Lemma f_U_weak' s f : f <= U_weak (s, f).
Proof. apply (f_U_weak (s, f)). Qed.

Lemma w_U_weak sf : w <= U_weak sf.
Proof.
assert (H : compan p b <= U sf) by apply (disim_const_below_ucompan _ _).
apply H.
Qed.

Lemma u_U_weak sf : u <= U_weak sf.
Proof.
etransitivity; [ apply (ucompan_below_wcompan p b) | apply w_U_weak ].
Qed.

Lemma id_U_weak sf : id <= U_weak sf.
Proof.
etransitivity; [ apply (id_below_wcompan p b) | apply w_U_weak ].
Qed.

Lemma U_weak_U sf : U_weak (U sf) <= U_weak sf.
Proof.
unfold U_weak; rewrite (ucompan_idempotent' _ _); reflexivity.
Qed.

Lemma comp_U_strong_weak sf : U_strong sf ° U_weak sf <= U_weak sf.
Proof.
change (snd_mon (D_s (U sf)) <= U_weak sf).
rewrite D_s_below_U, (ucompan_idempotent' _ _); reflexivity.
Qed.

Lemma comp_U_weak_w sf : U_weak sf ° w <= U_weak sf.
Proof.
change (snd_mon (Cw (U sf)) <= U_weak sf).
rewrite Cw_below_U, (ucompan_idempotent' _ _); reflexivity.
Qed.

Lemma U_strong_U_weak sf : U_strong sf <= U_weak sf.
Proof.
etransitivity; [ | apply comp_U_strong_weak ].
intro R; apply (U_strong sf).
apply id_U_weak.
Qed.

(* ========================================================================= *)
(* Properties of W_strong *)

Lemma s_W_strong sf : fst sf <= W_strong sf.
Proof.
assert (H : sf <= W sf) by apply (id_below_wcompan _ _).
apply H.
Qed.

Lemma u_W_strong sf : u <= W_strong sf.
Proof.
assert (H : compan p b <= W sf) by apply (disim_const_below_wcompan _ _).
apply H.
Qed.

Lemma id_W_strong sf : id <= W_strong sf.
Proof.
etransitivity; [ apply (id_below_ucompan p b) | apply u_W_strong ].
Qed.

Lemma U_W_strong sf : U_strong sf <= W_strong sf.
Proof.
unfold U_strong; rewrite (ucompan_below_wcompan _ _); reflexivity.
Qed.

Lemma W_strong_W sf : W_strong (W sf) <= W_strong sf.
Proof.
unfold W_strong; rewrite (wcompan_idempotent' _ _); reflexivity.
Qed.

Lemma comp_W_strong sf : W_strong sf ° W_strong sf <= W_strong sf.
Proof.
change (fst_mon (D_s (W sf)) <= W_strong sf).
rewrite D_s_below_U, (ucompan_below_wcompan _ _), (wcompan_idempotent' _ _).
reflexivity.
Qed.

(* ========================================================================= *)
(* Properties of W_weak *)

Lemma f_W_weak sf : snd sf <= W_weak sf.
Proof.
assert (H : sf <= W sf) by apply (id_below_wcompan _ _).
apply H.
Qed.

Lemma w_W_weak sf : w <= W_weak sf.
Proof.
assert (H : compan p b <= W sf) by apply (disim_const_below_wcompan _ _).
apply H.
Qed.

Lemma u_W_weak sf : u <= W_weak sf.
Proof.
etransitivity; [ apply (ucompan_below_wcompan p b) | apply w_W_weak ].
Qed.

Lemma id_W_weak sf : id <= W_weak sf.
Proof.
etransitivity; [ apply (id_below_wcompan p b) | apply w_W_weak ].
Qed.

Lemma U_W_weak sf : U_weak sf <= W_weak sf.
Proof.
unfold U_weak; rewrite (ucompan_below_wcompan _ _); reflexivity.
Qed.

Lemma W_weak_W sf : W_weak (W sf) <= W_weak sf.
Proof.
unfold W_weak; rewrite (wcompan_idempotent' _ _); reflexivity.
Qed.

Lemma comp_W_weak sf : W_weak sf ° W_weak sf <= W_weak sf.
Proof.
change (snd_mon (D_w (W sf)) <= W_weak sf).
rewrite D_w_below_W, (wcompan_idempotent' _ _); reflexivity.
Qed.

End HigherOrder.