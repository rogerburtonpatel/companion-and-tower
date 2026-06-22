From Stdlib Require Import Utf8.
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

(* Unproved claims:  *)

Section mon_progress. 
Context {X : Type} {CL : CompleteLattice X}.
Variable b : mon X. 
Variable progress : X → X → Prop.
Notation "R ↣ S" := (progress R S) (at level 70).
Context {PP : Progress progress}.

(* Claims below Definition 2.3 *)
(* 2 claims that definitions can definitions of progress and monotone functions
   can be interchanged: *)

Definition progress_mon := (fun R S => R <= b S).

(* Claim 1: R ↣ᵇ S ≜ R ⊑ b(S) *)
Lemma progress_mono (R S : X) : Progress progress_mon.
Proof. 
  constructor; intros; unfold progress_mon.  
  now transitivity Q. 
  now rewrite <- H. 
  apply sup_spec; intros. apply H. apply H0. 
Qed. 


(* NOT TRUE; CONTRAVARIANT ABOVE IS TRUE *)
Lemma mon_progress (R : X) : Proper (leq ==> leq) progress.
Proof. Abort. 

(* Claim 2: b(S) ≜ ⨆ R. R ↣ᵇ S *) (* Roughly *)
Lemma mon_progress (R : X) : Proper (leq ==> leq) (fun S => ∐ {R | R ↣ S}).
Proof. 
  repeat intro. apply leq_xsup. apply progress_limit_l. 
  intros. now rewrite <- H. 
Qed. 


(* The two claims above are each only *one half* of the correspondence in the
   remark below Definition 2.3: [progress_mono] turns a monotone function into a
   progress relation, and [mon_progress] shows the converse map lands in the
   monotone functions.  What the remark actually asserts is that these two maps
   are mutually inverse -- *that* is the content, and it is what the (false, as
   stated) [b_progress] above was groping at.  We make both round-trips precise.

   Note the original [b_progress] could not hold: it related an *arbitrary* [b]
   to an *arbitrary, unrelated* progress [↣].  The correspondence only pins down
   [b] from the progress relation it itself induces, and vice versa. *)

(* Round-trip 1  (function → relation → function).
   Reading the progress relation [progress_mon] induced by [b] back as a
   function recovers [b] exactly:   ⨆ {R | R ⊑ b S}  ==  b S. *)
Lemma mon_of_progress_mon S : (∐ {R | progress_mon R S}) == b S.
Proof.
  apply antisym.
  + apply sup_spec. intros R HR. exact HR.   (* each R ⊑ b S *)
  + apply leq_xsup. unfold progress_mon. reflexivity.   (* b S ⊑ b S, so b S is in the set *)
Qed.

(* The converse construction, packaged as a genuine monotone function: this is
   the answer to "monotone functions in terms of progresses".  From an abstract
   progress relation [↣] we build   b_↣ S  ≜  ⨆ {R | R ↣ S}. *)
Program Definition mon_of_progress : mon X :=
  {| body S := ∐ {R | R ↣ S} |}.
Next Obligation.
  intros S S' HS. apply sup_spec; intros R HR.
  apply leq_xsup. eapply progress_monotone_r; [ exact HS | exact HR ].
Qed.

(* Round-trip 2  (relation → function → relation).
   Reading [mon_of_progress] back as a progress relation recovers [↣]:
        R ↣ S   ↔   R ⊑ b_↣ S .
   Concretely [b_↣ S] is the *greatest* [R] with [R ↣ S], and this is exactly
   what makes "[R ↣ S]" mean nothing more than "[R ⊑ b_↣ S]" -- the meaning of
   the progress relation comes first (here, from [progress_limit_l]); the
   function is then extracted from it. *)
Lemma progress_mon_of S R : R ↣ S <-> R <= ∐ {Q | Q ↣ S}.
Proof.
  split.
  + intro H. now apply leq_xsup.
  + intro H. eapply progress_monotone_l; [ exact H | ].
    apply progress_limit_l. now intros Q HQ.
Qed.


End mon_progress.


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