(* Begin diacrit *)
From Stdlib Require Import Utf8.
Require Import lattice.
Require Import progress evolution.

Section Companion.
Context {X : Type} {CL : CompleteLattice X}.

Variable p : X → X → Prop.
Variable b : X → X → Prop.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (b R S) (at level 70).
Notation "f ↝ₚ g" := (p_evolution p f g) (at level 70).
Notation "f ↝ₐ g" := (a_evolution p b f g) (at level 70).

Definition compatible f := f ↝ₚ f ∧ f ↝ₐ f.
Definition compan := ∐ {f | compatible f}.

Notation u := (fst compan).
Notation w := (snd compan).

Context {PP : Progress p} {PB : Progress b}.

Lemma compan_compatible : compatible compan.
  Proof.
  split; apply progress_limit_l; intros f Hf.
  + apply progress_monotone_r with (Q:=f). 
  apply leq_xsup. assumption. 
  apply Hf. 
  + apply progress_monotone_r with (Q:=f). 
  apply leq_xsup. assumption. 
  apply Hf.
  Qed. 

Lemma ucompan_compatible : u ↝[p] u ∧ u ↝[b] w.
Proof. split; apply compan_compatible. Qed.

Lemma ucompan_p_compatible : u ↝[p] u.
Proof. apply compan_compatible. Qed.

Lemma ucompan_a_compatible : u ↝[b] w.
Proof. apply compan_compatible. Qed.

Lemma wcompan_compatible : w ↝[p] w ∧ w ↝[p # b] w.
Proof. split; apply compan_compatible. Qed.

Lemma wcompan_p_compatible : w ↝[p] w.
Proof. apply compan_compatible. Qed.

Lemma wcompan_a_compatible : w ↝[p # b] w.
Proof. apply compan_compatible. Qed.

Lemma compat_below_compan f : compatible f → f <= compan.
Proof. apply leq_xsup. Qed.

(* ------------------------------------------------------------------------- *)

Lemma id_compatible : compatible p_id.
Proof.
split; split; split; firstorder.
Qed.

Lemma id_below_compan : p_id <= compan.
Proof. apply compat_below_compan, id_compatible. Qed.

Lemma id_below_ucompan : id <= u.
Proof. apply id_below_compan. Qed.

Lemma id_below_wcompan : id <= w.
Proof. apply id_below_compan. Qed.

(* ------------------------------------------------------------------------- *)

Lemma compan2_compatible : compatible (compan • compan).
Proof.
split.
+ apply (p_evolution_comp p); apply compan_compatible.
+ apply (a_evolution_comp p b); apply compan_compatible.
Qed.

Lemma compan_idempotent : compan • compan <= compan.
Proof. apply compat_below_compan, compan2_compatible. Qed.

Lemma ucompan_idempotent : u ° u <= u.
Proof. apply compan_idempotent. Qed.

Lemma wcompan_idempotent : w ° w <= w.
Proof. apply compan_idempotent. Qed.

Lemma ucompan_idempotent' R : u (u R) <= u R.
Proof. apply ucompan_idempotent. Qed.

Lemma wcompan_idempotent' R : w (w R) <= w R.
Proof. apply wcompan_idempotent. Qed.

(* ------------------------------------------------------------------------- *)

Lemma compan_is_disim :
  compan = di_similarity (p_evolution p) (a_evolution p b).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)

Lemma disim_const_compatible :
  compatible (const (di_similarity p b), const (di_similarity p b)).
Proof.
split; split; simpl; split; intros; apply (di_similarity_sim p b).
Qed.

Lemma disim_const_below_compan :
  (const (di_similarity p b), const (di_similarity p b)) <= compan.
Proof. apply compat_below_compan, disim_const_compatible. Qed.

Lemma disim_const_below_ucompan : const (di_similarity p b) <= u.
Proof. apply disim_const_below_compan. Qed.

Lemma disim_const_below_wcompan : const (di_similarity p b) <= w.
Proof. apply disim_const_below_compan. Qed.

(* ------------------------------------------------------------------------- *)

Theorem soundness (R : X) :
  R ↣ₚ u R → R ↣ₐ w R → R <= di_similarity p b.
Proof.
intros Hpas Hact; transitivity (w (u R)).
+ rewrite <- id_below_ucompan, <- id_below_wcompan; reflexivity.
+ apply ucompan_compatible in Hpas; rewrite ucompan_idempotent' in Hpas.
  apply ucompan_compatible in Hact; rewrite wcompan_idempotent' in Hact.
  apply wcompan_compatible in Hact; [ | assumption ].
  apply wcompan_compatible in Hpas.
  rewrite wcompan_idempotent' in Hact.
  apply leq_xsup; split; [ assumption | ].
  eapply progress_monotone_r; [ | eassumption ].
  apply w, id_below_ucompan.
Qed.

Theorem soundness_f (s f : [X ⇒ X]) (R : X) :
  R ↣ₚ s R → R ↣ₐ f R → (s, f) <= compan → R <= di_similarity p b.
Proof.
intros Hs Hf Hsf; destruct Hsf as [ Hsu Hfw ].
apply soundness; eapply progress_monotone_r; try eassumption.
+ apply Hsu.
+ apply Hfw.
Qed.

(* ------------------------------------------------------------------------- *)

Lemma soundness_id_sim R :
  R ↣ₚ R → R ↣ₐ di_similarity p b → R <= di_similarity p b.
Proof.
intros Hpas Hact; apply (soundness_f id (const (di_similarity p b))).
+ assumption.
+ assumption.
+ split; [ apply id_below_ucompan | apply disim_const_below_wcompan ].
Qed.

End Companion.

Section CompanionUW.
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

Lemma ucompan_below_wcompan : u <= w.
Proof.
assert (Huu : (u, u) <= compan p b).
{ apply (soundness_id_sim (p_evolution p) (a_evolution p b)).
+ split; split; intros R S HRS; apply (ucompan_p_compatible p b); assumption.
+ split; split; intros R S.
  - apply (ucompan_a_compatible p b).
  - intros _; apply (ucompan_a_compatible p b).
}
destruct Huu; assumption.
Qed.

End CompanionUW.
