(** * Experiments: unifying the ordinary companion [t] with the diacritical
      companion [(u, w)].

   Everything here relates the single-function companion [t b] of a monotone
   function [b] to the diacritical companion [(u, w)] of a pair of progress
   relations, by *deriving* the progressions from monotone functions.

   - [Section pairs]: the collapsed case [p = a = progress_mon b].  Both
     diacritical components coincide with the ordinary companion: [u == t] and
     [w == t].
   - [Section diacritical_two]: two genuinely different progressions induced by
     [b1] (passive) and [b2] (active), combined as [b1 ⊓ b2].  Here [u] and [w]
     come apart and [w] escapes the combined companion. *)

From Stdlib Require Import Utf8 Setoid Morphisms.
Require Import lattice progress evolution companion diacritical_companion.
Require Import tactics.
Require Import utils. 

(* ========================================================================= *)
(* The collapsed case: a single [b], with both progressions induced by it. *)
Section pairs.
Context {X : Type} {CL : CompleteLattice X}.
Variable b : mon X.
Notation t := (t b).
Notation compat f := (f ° b <= b ° f) (only parsing).

(* Unify the theory: rather than taking [p], [a] as abstract progressions with a
   separate, unrelated [b] (and bolting them together with an [Hb] hypothesis),
   we *derive* both progressions from the monotone function [b] already in
   context.  [R ↣ S := R <= b S] is the progress relation induced by [b]
   ([progress_mon]/[progress_mono] from [progress.v]).  The diacritical
   companion [(u, w)] of [b] is then [compan p a] for [p = a = progress_mon b],
   and everything is stated over a single [b]. *)
Notation p := (progress_mon b).
Notation a := (progress_mon b).
Instance PP : Progress (progress_mon b) := progress_mono b.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (a R S) (at level 70).
Notation "f ↝ₚ g" := (p_evolution p f g) (at level 70).
Notation "f ↝ₐ g" := (a_evolution p a f g) (at level 70).

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).
Notation w := (snd compan).

(* With [p = a = progress_mon b] the connecting hypothesis is now definitional:
   [R ↣ₚ R ∧ R ↣ₐ R] is just [R <= b R], so the di-similarity of the pair is the
   greatest post-fixpoint of [b]. *)
Lemma di_similarity_gfp_eq : di_similarity p a == gfp b.
Proof.
  apply antisym.
  - (* di_similarity p a <= gfp b: each self-progressing R is a post-fixpoint. *)
    unfold di_similarity. apply sup_spec. intros R [HR _].
    apply leq_gfp. exact HR.
  - (* gfp b <= di_similarity p a: gfp b self-progresses in both p and a. *)
    apply leq_xsup. split; apply gfp_pfp.
Qed.

(* One step of the ordinary companion [t] respects the progress induced by [b]:
   this is just monotonicity of [t] followed by its compatibility [compat_t]. *)
Lemma t_step R S : R <= b S -> t R <= b (t S).
Proof.
  intro H. transitivity (t (b S)).
  - apply (Hbody t). exact H.
  - apply (compat_t b S).
Qed.

(* The passive companion [u] is below the ordinary companion [t]: [u] is
   compatible w.r.t. [b], using that [u] p-evolves to itself. *)
Lemma u_leq_t : u <= t.
Proof.
  apply leq_t. intro x.
  destruct (ucompan_p_compatible p a) as [Hu].
  apply (Hu (b x) x). unfold progress_mon. reflexivity.
Qed.

(* Conversely [(t, t)] is a compatible pair, so it lies below the diacritical
   companion [(u, w)].  This gives both [t <= u] and [t <= w]. *)
Lemma t_pair_compatible : compatible p a (t, t).
Proof.
  split.
  - (* p_evolution: t p-evolves to itself, in both components. *)
    split; constructor; intros R S H; apply t_step; apply H.
  - (* a_evolution. *)
    split.
    + (* aev_strong: t a-evolves to t. *)
      constructor. intros R S H. apply t_step, H.
    + (* aev_weak: t (p#a)-evolves to t. *)
      constructor. intros R S _ H. apply t_step, H.
Qed.

Lemma t_below_compan : (t, t) <= compan.
Proof. apply leq_xsup. exact t_pair_compatible. Qed.

(* Unification: the passive diacritical companion [u] coincides with the
   ordinary companion [t]. *)
Proposition u_t : u == t.
Proof.
  apply antisym.
  - apply u_leq_t.
  - apply (proj1 t_below_compan).
Qed.

Lemma t_leq_w : t <= w.
Proof. apply (proj2 t_below_compan). Qed.

(* In THIS (collapsed) setting [p = a = progress_mon b], the active companion
   also collapses to [t]: [pev_weak] independently forces [w ↝[p] w], i.e. [w]
   is fully [b]-compatible, so [w <= t] as well.  The diacritical pair is just
   [(t, t)].  The room for [w] to rise above [t] only opens up once the active
   progression genuinely differs from the passive one -- see [diacritical_two]. *)
Lemma w_leq_t : w <= t.
Proof.
  apply leq_t. intro x.
  destruct (wcompan_p_compatible p a) as [Hw].
  apply (Hw (b x) x). unfold progress_mon. reflexivity.
Qed.

Proposition w_t : w == t.
Proof. apply antisym; [ apply w_leq_t | apply t_leq_w ]. Qed.

End pairs.

(* ========================================================================= *)
(* The genuine diacritical setting: two DIFFERENT progressions, [p] induced by
   a passive [b1] and [a] induced by an active [b2].  The combined behaviour is
   [b := b1 ⊓ b2], and we probe how the diacritical companion [(u, w)] of
   [(p, a)] relates to the ordinary companions [t b1] (passive) and [t b]
   (combined).  This is where [u != w] and [w] escapes the combined companion. *)
Section diacritical_two.
Context {X : Type} {CL : CompleteLattice X}.
Variable b1 b2 : mon X.

Notation p := (progress_mon b1).
Notation a := (progress_mon b2).
#[local] Instance PP1 : Progress (progress_mon b1) := progress_mono b1.
#[local] Instance PP2 : Progress (progress_mon b2) := progress_mono b2.

Notation "R '↣ₚ' S" := (p R S) (at level 70).
Notation "R '↣ₐ' S" := (a R S) (at level 70).

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).
Notation w := (snd compan).

(* The combined behaviour is the meet, and the di-similarity of the pair is its
   greatest fixpoint: [R <= b1 R /\ R <= b2 R] iff [R <= (b1 ⊓ b2) R]. *)
Lemma di_similarity_meet_gfp : di_similarity p a == gfp (cap b1 b2).
Proof.
  apply antisym.
  - unfold di_similarity. apply sup_spec. intros R [H1 H2].
    apply leq_gfp. apply cap_spec. split; [ exact H1 | exact H2 ].
  - apply leq_xsup.
    pose proof (gfp_pfp (cap b1 b2)) as H. apply cap_spec in H.
    exact H.
Qed.

(* Both components are compatible w.r.t. the PASSIVE [b1] -- [pev_strong] for
   [u], [pev_weak] for [w] -- so both lie below the passive companion [t b1].
   This is the upper bound: [w] never rises above the passive companion. *)
Lemma u_below_t1 : u <= t b1.
Proof.
  apply leq_t. intro x.
  destruct (ucompan_p_compatible p a) as [Hu].
  apply (Hu (b1 x) x). unfold progress_mon. reflexivity.
Qed.

Lemma w_below_t1 : w <= t b1.
Proof.
  apply leq_t. intro x.
  destruct (wcompan_p_compatible p a) as [Hw].
  apply (Hw (b1 x) x). unfold progress_mon. reflexivity.
Qed.

Lemma u_below_w : u <= w.
Proof. apply (ucompan_below_wcompan p a). Qed.

(* Pinning down the bottom of [w]'s tower: [w bot] is *exactly* the combined
   bisimilarity, not an overshoot.

   - [<=]:  [bot] progresses (trivially, being least) to itself under both [p]
     and [a], and [w] preserves both progressions to itself ([wcompan_p_compatible]
     gives [w bot ↣ₚ w bot], [wcompan_a_compatible] gives [w bot ↣ₐ w bot]).
     So [w bot] self-progresses in both, hence sits in [di_similarity].
   - [>=]:  the constant [di_similarity] is below [w] ([disim_const_below_wcompan]),
     so [di_similarity <= w bot]. *)
Lemma w_bot_eq_di_similarity : w bot == di_similarity p a.
Proof.
  apply antisym.
  - apply leq_xsup. split.
    + destruct (wcompan_p_compatible p a) as [Hw].
      apply (Hw bot bot). unfold progress_mon. apply leq_bx.
    + destruct (wcompan_a_compatible p a) as [Hw'].
      apply (Hw' bot bot); unfold progress_mon; apply leq_bx.
  - apply (disim_const_below_wcompan p a bot).
Qed.

(* Hence [w]'s tower bottoms out at the combined bisimilarity: [w] is a *sound*
   enhancement -- its fixpoint from [bot] is the gfp, exactly like [t]. *)
Corollary w_bot_gfp : w bot == gfp (cap b1 b2).
Proof. rewrite w_bot_eq_di_similarity. apply di_similarity_meet_gfp. Qed.

(* Why the collapse argument from [Section pairs] breaks here, and what stays
   open:

   - [t b] for [b = b1 ⊓ b2] is compatible w.r.t. [b1 ⊓ b2], i.e.
     [t b ((b1 ⊓ b2) R) <= (b1 ⊓ b2)(t b R)].  But [pev_strong]/[pev_weak]
     demand compatibility w.r.t. [b1] ALONE: [R <= b1 S -> t b R <= b1 (t b S)].
     Knowing only [R <= b1 S] (not [R <= b2 S]) we cannot reach [R <= b S], so
     [t_step] no longer applies and [(t b, t b)] is NOT provably compatible.
     Hence the easy [t b <= w] route is gone.

   - The active asymmetry is now real: [u] must satisfy the *unconditional*
     [aev_strong]  [R <= b2 S -> u R <= b2 (w S)], while [w]'s only active
     obligation is the *conditional* [aev_weak]
     [R <= b1 R -> R <= b2 S -> w R <= b2 (w S)].  The extra premise [R <= b1 R]
     is what lets [w] exceed [t b].

   Conjecture (the [w > t b] phenomenon):  [t b <= w] with [t b < w] possible,
   so the combined companion is sandwiched:  [t (b1 ⊓ b2) <= w <= t b1]. *)
Lemma t_comb_below_w : t (cap b1 b2) <= w.
Proof.
Abort. 



Require Import tower rel. 
(* Notation Chain := (Chain (cap b1 b2)). *)
Notation "` x" := (elem x) (at level 2).

Notation b' := (cap b1 b2).

(* w preserves members of the chain of b1 *)
Proposition w_in_tower_b1 : forall x : Chain b1, w `x == `x. 
Proof.
  intros. apply antisym. 
  - rewrite w_below_t1. apply chain.t_chain. 
  - rewrite <- id_below_wcompan; try typeclasses eauto. 
  reflexivity. 
Qed. 
  
(* what about b'? *)

Proposition w_in_tower_b' : forall x : Chain b', `x <= w `x. 
Proof.
  intros. rewrite <- id_below_wcompan; try typeclasses eauto. 
  reflexivity. 
Qed. 




(* is w actually preserving tower membership? *)


(* etransitivity. 
    apply (rule_coind). 
    unshelve (instantiate (1:=_)).
    exact `x. 
    unshelve (instantiate (1:=_)).
    exact (b'). unfold bt. 
    cbn. Search cap. 
    Search ( _ <= t _).
  2: eapply chain.t_chain.
  transitivity (b1 (t b1 (cup `x (t b1 `x)))).
  shelve. 

  apply cap_spec. split. 
  apply b1.  

  - apply id_below_wcompan; typeclasses eauto. 
Abort.  *)


End diacritical_two.


Section example. 


CoInductive stream :=
 | τ (s : stream)
 | β (n : nat) (k:stream).

Notation "'τ' s"   := (τ s) (at level 35, right associativity).
Notation "'(β' n ')' k" := (β n k) (at level 35, n at level 0, k at level 35).

Variant b_passive (bisim : stream -> stream -> Prop) : stream -> stream -> Prop := 
| bisim_faux_beta n m s1 s2 : b_passive bisim ((β n) s1) ((β m) s2) 
| bisim_tau s1 s2 : bisim s1 s2 -> b_passive bisim (τ s1) (τ s2). 
Variant b_active (bisim : stream -> stream -> Prop) : stream -> stream -> Prop := 
| bisim_faux_tau s1 s2 : b_active bisim (τ s1) (τ s2) 
| bisim_beta n s1 s2 : bisim s1 s2 -> b_active bisim ((β n) s1) ((β n) s2). 

Program Definition b1 : mon (stream -> stream -> Prop) := {| body := b_passive |}.
Next Obligation. 
monauto. 
Qed. 

Program Definition b2 : mon (stream -> stream -> Prop) := {| body := b_active |}.
Next Obligation. 
monauto. 
Qed.

Definition bisim_passive := gfp b1. 
Definition bisim_active := gfp b2. 

Notation p := (progress_mon b1).
Notation a := (progress_mon b2).

Instance Pp : Progress p
         := progress_mono b1. 

Instance Pa : Progress a 
         := progress_mono b2. 

Notation compan := (diacritical_companion.compan p a).
Notation u := (fst compan).  
Notation w := (snd compan).  

Notation b' := (cap b1 b2).

(* 
CL mon X 
b' := b1 ∩ b2 
        
                                
        t b1 

        w bot = gfp 
        
        t b' (x) in the tower 

        
        ⊤
        b ⊤

        hole 
        ... 

        hole 

        gfp b 

R ↣ R := R bisimulation 



*)


Lemma disim_gfp : di_similarity p a == gfp b'. 
Proof.   
  apply antisym. 
  - unfold di_similarity. apply sup_spec. intros i [H H0]. 
  rewrite chain.gfp_tower. 
  repeat red. 
  coinduction c cih. intros. 
  apply H in H1 as H2.  
  apply H0 in H1 as H3.
  inv H2. 
  + split. 
    * constructor. 
    * inv H3. 
      constructor.
      apply cih. apply H4. 
  + split. 
    * constructor. 
      apply cih. inv H3.
    * constructor.  
  - apply leq_xsup. split; repeat red; intros. 
    all: apply (gfp_pfp b') in H.
    all: inv H. 
Qed. 

(* Proposition tb_leq_w : t b' <= w.
Proof. 
  repeat red.  
  intros sim s1 s2 Ht.
  exists (t b1, t b2). 
  2 : auto. 
  (* 4 cases *)
  split. 
  - constructor.
   (* 1: t b1 b1-evolves to t b1 *)
  + cbn. constructor. intros. 
    repeat red. intros. 
    repeat red in H.
    cbn in H0.  *)
        
    
    
(* Eval stop_here in True.  *)
End example. 
(* ========================================================================= *)
(** ** Higher-order: running the companion on the lattice of RELATIONS.

   The companion theory above is parametric in the carrier lattice [X].  Taking
   [X := A -> A -> Prop] with its *canonical* pointwise lattice
   ([CompleteLattice_dfun] over [CompleteLattice_Prop]) turns the abstract
   theory into concrete coinduction-up-to:

     - lattice elements        = relations on [A];
     - [<=]                     = relation inclusion;
     - [cap]/[cup]/[top]/[bot]  = intersection / union / full / empty relation;
     - a monotone [b : mon Rel] = a behaviour (an "observation" functor);
     - [gfp b]                  = the coinductively defined relation;
     - monotone [f : mon Rel]   = an up-to technique, and [t b] the greatest
                                  sound one; the diacritical [(u, w)] is its
                                  passive/active split.

   None of the *theorems* change -- they apply at [X := Rel] verbatim -- but
   this is the level where they have computational meaning. *)

Section relation_lattice.
Context {A : Type}.
Notation Rel := (A -> A -> Prop).

(* With the canonical instance the lattice operations are *definitionally* the
   relational ones, so the earlier [top] question is now provable (there is no
   abstract [c] to hide the order): [top] really is the full relation. *)
Lemma rel_top   : (top : Rel) = fun _ _ => True.  Proof. reflexivity. Qed.
Lemma rel_bot   : (bot : Rel) = fun _ _ => False. Proof. reflexivity. Qed.
Lemma rel_cap (R S : Rel) : cap R S = fun x y => R x y /\ S x y. Proof. reflexivity. Qed.
Lemma rel_cup (R S : Rel) : cup R S = fun x y => R x y \/ S x y. Proof. reflexivity. Qed.
Lemma rel_leq (R S : Rel) : (R <= S) <-> (forall x y, R x y -> S x y).
Proof. split; intro H; exact H. Qed.

(* The fixed version of the line-196 goal, over the canonical [dfun] lattice. *)
Lemma top_rel_refl (x : A) : (top : Rel) x x == True.
Proof. cbn. tauto. Qed.

End relation_lattice.

(* ------------------------------------------------------------------------- *)
(** A concrete behaviour: the simulation functor of a transition relation
    [step].  This grounds the abstract machinery -- [gfp sim] is similarity, and
    a coinductive proof about it is just a post-fixpoint witness fed to
    [leq_gfp]. *)

Section simulation.
Context {A : Type} (step : A -> A -> Prop).
Notation Rel := (A -> A -> Prop).

Program Definition sim : mon Rel :=
  {| body R := fun x y => forall x', step x x' -> exists2 y', step y y' & R x' y' |}.
Next Obligation.
  intros R S HRS x y H x' Hx'.
  destruct (H x' Hx') as [y' Hstep HR]. 
  exists y'; [ exact Hstep | exact (HRS x' y' HR) ].
Qed.

(* One-step unfolding of similarity, straight from [gfp_fp]. *)
Lemma similarity_unfold x y :
  gfp sim x y <-> forall x', step x x' -> exists2 y', step y y' & gfp sim x' y'.
Proof. exact (gfp_fp sim x y). Qed.

(* Reflexivity by coinduction: equality is a post-fixpoint of [sim]. *)
Lemma eq_below_similarity : (fun a b : A => a = b) <= gfp sim.
Proof.
  apply leq_gfp. intros a b Hab a' Ha'.
  exists a'; [ rewrite <- Hab; exact Ha' | reflexivity ].
Qed.

Lemma similarity_refl x : gfp sim x x.
Proof. exact (eq_below_similarity x x eq_refl). Qed.

(* Transitivity by coinduction: relational composition is a post-fixpoint.
   Packaged as a technique this is exactly "up-to-transitivity", which lives
   below the companion [t sim]. *)
Lemma comp_below_similarity :
  (fun x z => exists y, gfp sim x y /\ gfp sim y z) <= gfp sim.
Proof.
  apply leq_gfp. intros x z [y [Hxy Hyz]] x' Hx'.
  pose proof (proj1 (similarity_unfold x y) Hxy x' Hx') as [y' Hyy' Hx'y'].
  pose proof (proj1 (similarity_unfold y z) Hyz y' Hyy') as [z' Hzz' Hy'z'].
  exists z'; [ exact Hzz' | exists y'; split; assumption ].
Qed.

Lemma similarity_trans x y z : gfp sim x y -> gfp sim y z -> gfp sim x z.
Proof.
  intros Hxy Hyz. apply (comp_below_similarity x z). exists y; split; assumption.
Qed.

(* The abstract diacritical results transfer for free.  With [sim] used as both
   the passive and active progression, the passive companion [u] is just the
   ordinary companion [t sim] -- this is [u_t] instantiated at [Rel]. *)
#[local] Instance Psim : Progress (progress_mon sim) := progress_mono sim.

Example similarity_passive_companion :
  fst (compan (progress_mon sim) (progress_mon sim)) == t sim.
Proof. exact (u_t sim). Qed.

  (* w's image is in the tower *)

End simulation.