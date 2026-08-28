From Stdlib Require Import Logic.FunctionalExtensionality. 
From Stdlib Require Import Logic.PropExtensionality. 


From Stdlib Require Import Utf8 Setoid Morphisms.
Require Import progress evolution companion diacritical_companion.
Require Import lattice tower.
(* Require Import experiments. *)
Require Import tactics.
Require Import utils. 


Section combined_b.

  (* setup: types, lattice, monotone functions. 
     [b] may be the cup of a passive bp and an active ba. *)
Context {X : Type} {CL : CompleteLattice X}.
Variable b bp ba : mon X.
Hypothesis Hb : ba <= b. 
 
(* Lemmas 

test: gfp ba -> gfp b  *)
Lemma ba_b : gfp ba <= gfp b.  
Proof.
  now rewrite Hb.  
Qed. 

Lemma inf_bot_weq_top : inf bot == @top (X -> Prop) _.
Proof. 
  apply antisym. 
  apply leq_xt. 
  apply inf_spec. intros; easy. 
Qed.  

(* this is not true *)
Lemma ba_b_tower  (cb : Chain b) (cba : Chain ba) : 
  elem cba <= elem cb. 
Proof. 
  (* problem: the tower tactic greedily slurps up the first chain 
  it can find. we need a way to have it always be the last elem... or not, 
  maybe that breaks something. but it is annoying. *)
  (* we must use b or this breaks. *)
  eapply (@tower _ _ b).
  (* if T is bottom (tower ba) fails because we have to prove top <= elem cb, 
  which is not (always) true *)
  { repeat intro. apply inf_spec. intros. now apply H.  }
  intros. rewrite <- Hb at -2. 
  rewrite <- H.
   (* wrong direction. problems.  *)
Abort. 

Lemma ba_le_b (cb : Chain b) (cba : Chain ba) : 
  ba (elem cb) <= b (elem cb). 
Proof.
  now rewrite Hb.
Qed.   


Variable ba' : mon (X -> Prop).
Lemma C_inf_bot : C ba' (inf (@bot ((X -> Prop) -> Prop) _)). 
apply Cinf, leq_bx. 
Qed. 

Lemma inf_bot_top : 
(@top (X -> Prop) _) = (inf (@bot ((X -> Prop) -> Prop) _)). 
Proof. extensionality a; apply propositional_extensionality; symmetry; apply inf_bot_weq_top. 
Qed. 

Program Definition chain_weq_top x (Hweqtop : x == @top (X -> Prop) _) := {| elem := x |}. 
Next Obligation. 
replace x with (@top (X -> Prop) _) by (extensionality a; now apply propositional_extensionality). 
replace (@top (X -> Prop) _) with (inf (@bot ((X -> Prop) -> Prop) _)) by 
(extensionality a; apply propositional_extensionality, inf_bot_weq_top). 
apply C_inf_bot. 
Qed. 

Program Definition chain_inf_bot := {| elem := inf (@bot ((X -> Prop) -> Prop) _) |}. 
Next Obligation.
replace (λ a : X, ∀ i : X → Prop, bot i → Datatypes.id i a)
with (inf (@bot ((X -> Prop) -> Prop) _)) by reflexivity. 
apply Cinf, leq_bx. Qed. 

Program Definition chain_inf_bot2 := {| elem := inf (@bot (X -> Prop) _) |}. 
Next Obligation.
apply Cinf, leq_bx. Qed. 


(* this is quite sensible. elements do not have to be compared in lockstep. *)
Lemma not_ba_b_tower : ~ forall (cb : Chain b) (cba : Chain ba) ,
  elem cba <= elem cb. 
Proof. 
  intros contra. 
  specialize (contra (chain_gfp b) (chain_inf_bot2)).
  cbn in contra. 
(* here we have top <= gfp, which is a bit silly.
   proving false from it is something to do later...
    we need to push ba and b inside the proof. 
*)
Abort. 

(* what if we could compare 'like' elements? *)

(* 
⊤
<= 
b ⊤
<= 
ba <= ⊤

<= 
...
gfp b 
<= gfp ba
*)

(* what does it mean to compare like elements? *)
(* size of types (# constructors/order) is the same 
isomorphic up to the structure of b *)

(* a bit stronger, still quite straightforward *)
(* coinduction library fix: elem should be a coersion or canonical projection *)
Lemma ba_preserves_le (cb1 cb2 : Chain b) 
  (Helem: elem cb1 <= elem cb2) :
  ba (elem cb1) <= b (elem cb2). 
Proof.
  now rewrite Helem. 
Qed.

(* we want to state this: *)

Lemma proof_by_active_enough (cba : Chain ba) (cb : Chain b) :
      ba (elem cba) <= b (elem cb). 
(* but this is stated in a way that is subtly wrong: 
elem cba and elem cb need not be "the same element". *)
Abort. 

(* we must put a constraint. *)
Lemma proof_by_active_enough_weak (cba : Chain ba) (cb : Chain b) 
  (Helem: elem cba <= elem cb) : 
  ba (elem cba) <= b (elem cb).
Proof.
  now rewrite Helem. 
Qed.

(* obviously true at the gfp *)

End combined_b.

Section tests. 

Context {X : Type} {CL : CompleteLattice X}.
Variable b bp ba : mon (X -> X -> Prop).
Hypothesis Hb : ba <= b. 

Lemma gfp_ba_le_bchain (cb : Chain b) : gfp ba <= elem cb. 
Proof.
  rewrite Hb. 
  apply gfp_chain. 
Qed. 

Hypothesis HProperActive : forall (cba : Chain ba), Proper (gfp b ==> eq ==> iff) (elem cba).
Hypothesis HProperActive_after : forall (cb : Chain b), Proper (gfp b ==> eq ==> iff) (ba (elem cb)).
Variables x y z : X. 
Variable cb : Chain b. 
Hypothesis CONDITIONAL_UPTO : gfp b x z. 


Goal ba (elem cb) <= elem cb. 
transitivity (b (elem cb)).
apply Hb. 
apply b_chain. 
Qed. 

Goal elem cb x y.
  (* we cannot use our conditional up-to technique. *)
  Fail rewrite CONDITIONAL_UPTO. 
  Fail eapply HProperActive. 
  Fail eapply HProperActive_after.
  accumulate acc.  
  apply Hb. 
  rewrite CONDITIONAL_UPTO. 
Abort.
  (* clear HProperActive. (* we actually won't need this one. *)

  step.
  apply Hb. 
  
  (* now we can use a weird trick: 
  we can rewrite _knowing_ we will take an active step... *)
  rewrite CONDITIONAL_UPTO. 
  apply ACTIVE_STEP.
Qed.  *)


End tests. 
