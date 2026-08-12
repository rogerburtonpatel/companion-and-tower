
(** * tests for the exported tactics *)

Require Import all.
Import CoindNotations.
    
Section s.

  (** on binary relations on natural numbers *)
  Variables b c s: mon (nat -> nat -> Prop).
  (* Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (` R x y) (at level 80).
  Notation "x ≡ y" := (` _ x y) (at level 80).
  Notation "x [≡] y" := (b ` _ x y) (at level 80). *)

  (* Goal gfp b 5 6 /\ gfp c 7 8.
    Fail coinduction R H.
  Abort. *)

  (* FIXES *)
Goal gfp b 0 0 -> gfp b 1 1.
  apply gfp_prop.
  intro x.
  apply tower. 
    Fail apply_ptower x 0. 
Abort.
  (* TODO: make this work:  *)
  Goal gfp b 5 6 -> gfp b 7 8.
    apply gfp_prop. intro x. 
    Fail apply_ptower x 0. 
  Abort. 


End s.

(** ** [accumulate] on hypotheses of the shape [f (elem R) u v]

    such hypotheses are recorded in the [Ts] list together with the function
    [f] they apply to the candidate, and are carried through untouched.
    extracted from [human_experiments.v], section [tests]. *)

Section accumulate_body.

  Context {X: Type} {CL: CompleteLattice X}.
  Variables b ba: mon (X -> X -> Prop).
  Variables x y z: X.
  Variable cb: Chain b.

  (** through a foreign monotone function *)
  Goal ba (elem cb) z y -> elem cb x y.
    intro ACTIVE_STEP.
    accumulate acc.
  Abort.

  (** through [b] itself *)
  Goal b (elem cb) z y -> elem cb x y.
    intro h.
    accumulate acc.
  Abort.

  (** under a quantifier *)
  Goal (forall n, ba (elem cb) n n) -> elem cb x y.
    intro h.
    accumulate acc.
  Abort.

  (** nested applications compose into a single monotone function *)
  Goal (forall n, ba (ba (elem cb)) n n) -> elem cb x y.
    intro h.
    accumulate acc.
  Abort.

  Goal ba (b (elem cb)) z y -> elem cb x y.
    intro h.
    accumulate acc.
  Abort.

  (** a hypothesis must be uniform: all its leaves apply the same function to
      the candidate for technical reasons of reification. 
      but this is not needed for cases like this, and we 
      may be able to do better. *)
  Goal elem cb z y /\ ba (elem cb) x y -> elem cb x y.
    intro h.
    Fail accumulate acc.
  Abort.

  Goal elem cb z y /\ ba (gfp b) x y -> elem cb x y.
    intro h.
    Fail accumulate acc.
  Abort.

  (** splitting the conjunction into separate hypotheses lifts the restriction:
      each one becomes its own [Ts] entry, with its own function *)
  Goal elem cb z y -> ba (elem cb) x y -> elem cb x y.
    intros h1 h2.
    accumulate acc.
  Abort.

  (** and a hypothesis not mentioning the candidate is never reverted at all *)
  Goal elem cb z y -> ba (gfp b) x y -> elem cb x y.
    intros h1 h2.
    accumulate acc.
  Abort.

  (** a hypothesis directly about the candidate still works *)
  Goal elem cb z y -> elem cb x y.
    intro h.
    accumulate acc.
  Abort.

  (** the conclusion itself may not be about a function of the candidate *)
  Goal elem cb z y -> b (elem cb) x y.
    intro h.
    Fail accumulate acc.
  Abort.

End accumulate_body.


(* TO FIX *)
Require Import infclosed. 


(* #1: Confusing behavior with coersions *)
Goal forall (b : mon (nat -> nat -> Prop)) (c : Chain b), 
elem c 4 5 -> elem c 5 6. 
Fail tower induction. (* correct, [c] is not introduced yet *)
intros b c.
tower induction.  

intros CIH Hb. 
(* Here we can clearly see the goal is [b `c 5 6]. *)
(* but matching on the exact goal we see does not work. *)
Fail lazymatch goal with 
| |- b `c 5 6 => idtac "found b"
end.
Set Printing All. 
(* Indeed, this is because of the [body] coersion of [b].
   [Set Printing All] shows us the culprit, but it is still confusing, 
   and it makes it hard to write and debug tactics.  *)
lazymatch goal with 
| |- @body _ _ _ _ _ _ _ _ => idtac "found b"
end.
Abort. 

(* bigger issues *)
(* mixed fixpoints *)
(* monotonicity of nested/composed monotone functions *)
(* diacritical support *)