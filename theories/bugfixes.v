
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
  Set Debug "backtrace".
    Fail apply_ptower x 0. 
Abort.
  (* TODO: make this work:  *)
  Goal gfp b 5 6 -> gfp b 7 8.
    apply gfp_prop. intro x. 
    Fail apply_ptower x 0. 
  Abort. 


End s.

(** ** [accumulate] rejects hypotheses of the shape [f (elem R) u v]

    reification only recognises [elem R u v] at the leaves, so any hypothesis
    stating that a pair belongs to some monotone function *applied to* the
    candidate is reported as an unsupported subterm.
    extracted from [human_experiments.v], section [tests]. *)

Section accumulate_body.

  Context {X: Type} {CL: CompleteLattice X}.
  Variables b ba: mon (X -> X -> Prop).
  Variables x y z: X.
  Variable cb: Chain b.

  (** through a foreign monotone function:
      [[coinduction] unsupported subterm (App): ba `cb z y] *)
  Goal ba (elem cb) z y -> elem cb x y.
    intro ACTIVE_STEP.
    Fail accumulate acc.
  Abort.

  (** through [b] itself, which is no better:
      [[coinduction] unsupported subterm (App): b `cb z y] *)
  Goal b (elem cb) z y -> elem cb x y.
    intro h.
    Fail accumulate acc.
  Abort.

  (** for comparison, a hypothesis directly about the candidate is fine *)
  Goal elem cb z y -> elem cb x y.
    intro h.
    accumulate acc.
  Abort.

End accumulate_body.
