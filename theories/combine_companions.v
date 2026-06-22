From Stdlib Require Import Utf8 Setoid Morphisms. 
Require Import lattice progress evolution companion diacritical_companion. 
Require Import tactics. 

Section Unproved_theorems. 
Context {X : Type} {CL : CompleteLattice X}.
Variable b : mon X. 
(* Variable p : relation X. 
Context {PP : Progress p}. *)

Notation "R '↣ᵇ' S" := (progress_mon b R S) (at level 70).

(* Progress-monotone equivalence *)



(* Other theorems not proved in the paper or development, TODO move eventually *)
Lemma progress_compan_below_gfp R : R ↣ᵇ t b R -> R <= gfp b.
Proof.
    intros.
    Locate coinduction. 
    apply companion.coinduction.
    unfold progress_mon in H. apply H.
Qed.


(* The coinductive object [ν(↣ᵇ)] of the induced progress relation -- its
   [similarity] -- is just the greatest fixpoint [gfp b] of [b]. *)
Lemma similarity_progress_gfp : similarity (progress_mon b) == gfp b.
Proof.
  apply antisym.
  + apply sup_spec. intros R HR. apply leq_gfp. apply HR.
  + apply leq_xsup. apply gfp_pfp.
Qed.

(** Theorem 2.6:  if [R ↣ᵇ t(R)] then [R ∈ ν(↣ᵇ)].

    The conclusion [R ∈ ν(↣ᵇ)] is [R ⊑ similarity (↣ᵇ)], and
    [similarity (↣ᵇ) = gfp b] by [similarity_progress_gfp]; so this is the
    [ν]-phrased version of [progress_compan_below_gfp].  The crux is that [t R]
    is a plain post-fixpoint of [b]:
        t R ⊑ t (b (t R))        (monotonicity of t applied to the hypothesis)
            ⊑ b (t (t R))        (compatibility:  t ∘ b ⊑ b ∘ t)
            ⊑ b (t R)            (t ∘ t ⊑ t). *)
Theorem thm_2_6 R : R ↣ᵇ t b R -> R <= similarity (progress_mon b).
Proof.
  unfold progress_mon. intro H.
  rewrite similarity_progress_gfp.
  assert (Hpost : t b R <= b (t b R)).
  { transitivity (t b (b (t b R))).
    - apply (Hbody (t b)). exact H.
    - transitivity (b (t b (t b R))).
      + apply (compat_t b (t b R)).
      + apply (Hbody b). apply (tt_t b R). }
  transitivity (t b R).
  - apply (id_t b R).
  - apply leq_gfp. exact Hpost.
Qed.

(* Correlary 2.7 *)

End Unproved_theorems. 

Section with_tower. 
Require Import tower rel. 
Context {X : Type} {CL : CompleteLattice X}.
Variable b : mon X. 
Notation t := (t b). 
Notation C := (C b).
Notation Chain := (Chain b).
Notation "` x" := (elem x) (at level 2).
(* the codomain of t is the tower; t on tower elements is the identity *)
Notation t' := (chain.t' b). 
 Notation compat f := (f ° b <= b ° f) (only parsing).

Lemma t'_of_tower_id : forall x : Chain, t' `x == `x.
Proof. 
  intros R. apply antisym. 
  rewrite <- chain.tt'; apply chain.t_chain.
  cbn; unfold chain.t'_, chain.C_. 
  apply inf_spec. 
  tauto. 
Qed.

Lemma t_of_tower_id : forall x : Chain, t `x == `x. 
intros. rewrite chain.tt'. apply t'_of_tower_id. 
Qed. 

Goal forall x, (C (t' x)).
intros. constructor. repeat intro. now inversion H. 
Qed. 


Lemma compat_in_tower f : compat f -> forall x, C (f x).
  intros H x. 
  apply leq_t in H. rewrite chain.tt' in H. 
  Fail rewrite H. 
   (* morally this feels true, but how convince rocq? *)
Abort. 

Definition sound (g : mon X) := forall x, 
  x <= b (g x)
-> x <= gfp b. 

Lemma compat_sound g : compat g -> sound g.
Proof. 
  intros H. 
  apply leq_t in H as Ht.  
  repeat intro.
  rewrite <- chain.gfp_tower.
  apply coinduction. unfold bt.
  rewrite <- Ht. 
  apply H0. 
Qed. 

(* companion is a valid enhancement, theorem 3.6 of pous. 
probably a shorter proof exists, 
but this was the one I came up with on my first go. *)
Lemma t_sound_ : gfp (bt b) == gfp b. 
Proof. 
  apply antisym. 
  rewrite <- 2 chain.gfp_tower. 
  eapply coinduction. unfold bt. 
  rewrite <- companion.gfp_fp. reflexivity. 
  apply gfp_leq. intro x. apply b. 
  now apply rule_done. 
Qed.  

Lemma t_sound : sound t. 
Proof. 
    intros x H. 
    rewrite <- chain.gfp_tower. 
    now apply coinduction. 
Qed. 

Lemma sound_below_t g : sound g <-> g <= t. 
Proof. 
Abort. 

Lemma sound_in_tower g : sound g -> forall x : Chain, g `x <= `x. 
Proof. 
  intros H x. 
  


End with_tower. 

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


End Companion. 