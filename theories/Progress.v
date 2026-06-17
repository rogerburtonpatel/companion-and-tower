Require Import Utf8.
Require Import Setoid.
Require Import lattice.

Section Progress.
Context {X : Type} {CL : CompleteLattice X}.

Variable progress : X → X → Prop.
Notation "R ↣ S" := (progress R S) (at level 70).

Class Progress : Prop :=
  { progress_monotone_l : ∀ R Q S : X, R <= Q → Q ↣ S → R ↣ S
  ; progress_monotone_r : ∀ R Q S : X, Q <= S → R ↣ Q → R ↣ S
  ; progress_limit_l    : ∀ (A : X → Prop) S,
      (∀ R, A R → R ↣ S) → (sup (fun R => A R)) ↣ S
      (* ∀ A : subset LL, ∀ S : X, R ∈ A → R ↣ S → sup A ↣ S *)
  }.

Context {PP : Progress}.
Global Instance progress_Proper :
  Morphisms.Proper (leq --> leq ++> Basics.impl) progress.
Proof.
intros R R' HR S S' HS H.
eapply progress_monotone_l; [ eassumption | ].
eapply progress_monotone_r; [ eassumption | ].
assumption.
Qed.

Definition similarity := ∐ {R | R ↣ R}.

Lemma sim_similarity : similarity ↣ similarity.
Proof.
apply progress_limit_l.
intros R Rsim; eapply progress_monotone_r; [ | eassumption ].
apply leq_xsup; assumption.
Qed.

(** indexed form of the left-limit law: progress is preserved under arbitrary
    indexed suprema.  This is the form actually needed once progress is lifted
    to the lattices of monotone functions and of products, where suprema are
    computed pointwise/componentwise rather than as [sup' _ id]. *)
Lemma progress_limit_l' {I} (P : I → Prop) (h : I → X) S :
  (∀ i, P i → h i ↣ S) → sup' P h ↣ S.
Proof.
intro H.
apply progress_monotone_l with (Q := sup (fun x => ∃ i, P i ∧ h i = x)).
+ apply sup_spec; intros i Pi. apply leq_xsup. exists i. split; [ exact Pi | reflexivity ].
+ apply progress_limit_l; intros x [ i [ Pi <- ] ]. now apply H.
Qed.

End Progress.

Arguments progress_monotone_l {X CL progress _}.
Arguments progress_monotone_r {X CL progress _}.
Arguments progress_limit_l    {X CL progress _}.

Section DiProgress.
Context {X : Type} {CL : CompleteLattice X}.

Variable p : X → X → Prop.
Variable b : X → X → Prop.

Context {PP : Progress p} {PB : Progress b}.
Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (b R S) (at level 70).

Definition di_similarity := ∐ {R | R ↣ₚ R ∧ R ↣ₐ R}.

Lemma di_similarity_p_sim : di_similarity ↣ₚ di_similarity.
Proof.
apply progress_limit_l; intros R HR.
eapply progress_monotone_r; [ | apply HR ].
apply leq_xsup; assumption.
Qed.

Lemma di_similarity_a_sim : di_similarity ↣ₐ di_similarity.
Proof.
apply progress_limit_l; intros R HR.
eapply progress_monotone_r; [ | apply HR ].
apply leq_xsup; assumption.
Qed.

Lemma di_similarity_sim : 
  di_similarity ↣ₚ di_similarity ∧ di_similarity ↣ₐ di_similarity.
Proof. split; [ apply di_similarity_p_sim | apply di_similarity_a_sim ]. Qed.

End DiProgress.