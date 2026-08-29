(** Behavioural claims made in the writeup, as a file that must compile.

    Each [Fail] pins a failure the rewritten library is expected to produce, and
    each bare tactic call pins a success. Compile with run-probes.sh. *)

From Coinduction Require Import all.
Import CoindNotations.

Section claims.
  Variables b c s : mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).

  (** claim 1: coinduction applies to a goal with the same gfp in a premise.
      This is the case the OCaml plugin rejected, and the reason
      InteractionTrees carried [unfold X at 2] and [iunfold_coind]. *)
  Goal gfp b 5 6 -> gfp b 7 8.
    coinduction R H.
  Abort.

  (** claim 2: a different gfp in a premise is also fine *)
  Goal gfp c 1 2 -> gfp b 5 6.
    coinduction R H.
  Abort.

  (** claim 3: two different gfps in the conclusion are still rejected, with a
      message that says so *)
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail coinduction R H.
  Abort.

  (** claim 4: the candidate may be named after a binder of the goal itself *)
  Goal forall R, R ~ R.
    coinduction R H.
  Abort.

  (** claim 5: stepping, and only one step at a time *)
  Goal 5 ~ 6.
    step. Fail step. unstep. Fail unstep.
  Abort.

  (** claim 6: stepping reaches a fixpoint hidden behind a definition *)
  Definition bsim := gfp b.
  Goal bsim 5 6.
    step.
  Abort.
End claims.

(** claim 7: everything above also works when the lattice is not a binary
    relation. This is the arity InteractionTrees needs for up-to bind, and the
    arity at which [apply sub_bChain] does not type. *)
Section arity.
  Variable b : mon (nat -> bool -> nat + bool -> unit -> Prop).

  Goal gfp b 4 true (inl 5) tt.
    coinduction R H.
  Abort.
  Goal gfp b 4 true (inl 5) tt.
    step. Fail step. unstep.
  Abort.
  Goal forall R : Chain b, elem R 4 true (inl 5) tt.
    intro R. step.
  Abort.
End arity.

(** claim 8: inf-closedness of the relation classes is discharged automatically
    at that arity too, which is what [tower induction] needs. *)
Section classes.
  Variable T : Type -> Type.
  Variables (X : Type) (RR : X -> X -> Prop).
  Notation L := (forall X Y, (X -> Y -> Prop) -> T X -> T Y -> Prop).
  Variable Q : T X -> T X -> Prop.

  Goal inf_closed (fun x : L => Reflexive  (x X X RR)). icauto. Qed.
  Goal inf_closed (fun x : L => Symmetric  (x X X RR)). icauto. Qed.
  Goal inf_closed (fun x : L => Transitive (x X X RR)). icauto. Qed.
  Goal inf_closed (fun x : L => Proper (Q ==> Q ==> iff) (x X X RR)). icauto. Qed.
  Goal inf_closed (fun x : L => Proper (Q ==> Q ==> Basics.flip Basics.impl) (x X X RR)). icauto. Qed.
End classes.

(** claim 9: monotonicity of a functor given by an inductive relation
    transformer is proved by the same [monauto] as the structural goals. *)
Section functor.
  Variables (A : Type) (red : A -> A -> Prop).
  Inductive simF (sim : A -> A -> Prop) : A -> A -> Prop :=
  | sim_now   x y   : red x y -> simF sim x y
  | sim_later x y z : red x y -> sim y z -> simF sim x z.

  Goal Proper (leq ==> leq) simF. Proof. monauto. Qed.
End functor.
