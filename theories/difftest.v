(** * side-by-side comparison of the plugin tactic and the reification-free one

    every goal below is run twice: once with [coinduction] (OCaml plugin,
    via reification) and once with [coinduction'] ([infclosed.v], via [tower]
    and [pattern]).  the two [Show]s must print the same proof state, 
    binder names included, since preserving them is the whole point.

    shapes are taken from [tests.v]. *)

Require Import all.
Require Import infclosed.
Import CoindNotations.

Section binary.

  Variables b c: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).

  Goal 5 ~ 6.
    coinduction R H. Show.
  Abort. 
  Goal 5 ~ 6.
    coinduction' R H. Show.
  Abort.

  Goal 5 ~ 6 /\ 7 ~ 8.
    coinduction R H. Show. 
  Abort. 
  Goal 5 ~ 6 /\ 7 ~ 8.
    coinduction' R H. Show.
  Abort.

  Goal forall n, n+n ~ n+n.
    coinduction R H. Show. 
  Abort. 
  Goal forall n, n+n ~ n+n.
    coinduction' R H. Show.
  Abort.

  Goal forall n m (k: n=m), n+n ~ m+m.
    coinduction R H. Show. 
  Abort. 
  Goal forall n m (k: n=m), n+n ~ m+m.
    coinduction' R H. Show.
  Abort.

  Goal forall n m (k: n=m), n+n ~ m+m /\ forall j, n+j ~ j+m.
    coinduction R H. Show. 
  Abort. 
  Goal forall n m (k: n=m), n+n ~ m+m /\ forall j, n+j ~ j+m.
    coinduction' R H. Show.
  Abort.

  (** candidate in negative position *)
  Goal gfp b 5 6 -> gfp b 7 8.
    coinduction R H. Show. 
  Abort. 
  Goal gfp b 5 6 -> gfp b 7 8.
    coinduction' R H. Show.
  Abort.

  (** two distinct coinductive predicates; both must refuse *)
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail coinduction R H.
    Fail coinduction' R H.
    (* debug: wrong error message. *)
  Abort.

End binary.

Section quaternary.

  Variable b: mon (nat -> bool -> (nat+bool) -> unit -> Prop).

  Goal gfp b 4 true (inl 5) tt.
    coinduction R H. Show. 
  Abort. 
  Goal gfp b 4 true (inl 5) tt.
    coinduction' R H. Show.
  Abort.

  Goal forall d, gfp b 3 d (inr d) tt.
    coinduction R H. Show. 
  Abort. 
  Goal forall d, gfp b 3 d (inr d) tt.
    coinduction' R H. Show.
  Abort.

  (* works at any arity *)
End quaternary.

(** the remaining [coinduction] shapes from [tests.v]: symmetric-function goals
    and dependent arities. *)

Section symmetric_shapes.

  Variable s: mon (nat -> nat -> Prop).
  Notation b' := (cap s (converse ° s ° converse)).

  Goal forall n m, gfp b' n m.
    coinduction R H. Show. 
  Abort. 
  Goal forall n m, gfp b' n m.
    coinduction' R H. Show.
  Abort.

  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall b, gfp b' (b+m) (n+b)).
    coinduction R H. Show. 
  Abort. 
  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall b, gfp b' (b+m) (n+b)).
    coinduction' R H. Show.
  Abort.

End symmetric_shapes.

Section dependent_arity.

  Variable T: nat -> Type.
  Variable f: forall n, T n.
  Variable b: mon (forall n, T n -> T (n+n) -> Prop).

  Goal gfp b _ (f 2) (f 4).
    coinduction R H. Show. 
  Abort. 
  Goal gfp b _ (f 2) (f 4).
    coinduction' R H. Show.
  Abort.

End dependent_arity.

(** ** [accumulate] from plugin vs [accumulate'] *)

Section accum.
  Variable b: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).

Ltac accum' cih :=
match goal with 
|- context[elem ?R] => 
  generalize dependent R; 
  intro R; 
  pattern (elem R);
  apply tower; [icauto|]
  (* intro R *)
  end. 


  (* one accumulated hypothesis *)
  Goal 5 ~ 6.
    coinduction R H. cut (` R 4 5). admit.
    accumulate H'. Show. 
  Abort. 
  Goal 5 ~ 6.
    coinduction' R H. cut (` R 4 5). admit.
    accumulate' H2. 
  Abort.

  (* the chain from tests.v: 1, then 2, then 3 hypotheses *)
  Goal 5 ~ 6.
    coinduction R H.
    cut (` R 4 5). admit. accumulate H'.
    cut (` R 3 2). admit. accumulate H''.
    cut ((forall x, ` R x 1) /\ ` R 0 18). admit. accumulate [H''' H''''].
    Show.
  Abort. 
  Goal 5 ~ 6.
    coinduction' R H.
    cut (` R 4 5). admit. accumulate' H'.
    cut (` R 3 2). admit. accumulate' H''.
    cut ((forall x, ` R x 1) /\ ` R 0 18). admit. accumulate' [H''' H''''].
    Show.
  Abort.
End accum.
