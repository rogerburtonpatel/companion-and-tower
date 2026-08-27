
(** * tests for the exported tactics *)

From Stdlib Require Import Program.Tactics. (* [revert_last], used in the manual symmetry test below *)
Require Import all.
Require Import infclosed.
Import CoindNotations.

(** ** [icauto] *)

Goal inf_closed (fun P : nat -> bool -> nat + bool -> unit -> Prop => P 4 true (inl 5) tt).
  icauto.
Qed.

Section h.
  Variable T: nat -> Type.
  Variable f: forall n, T n.

Goal inf_closed (fun P : forall n : nat, T n -> T (n + n) -> Prop => P 2 (f 2) (f 4)).
  icauto.
Qed.
End h.

(** ** [tower induction] *)

Ltac test_nat_goal :=
first [
  (lazymatch goal with
|- (elem _ _ _ -> elem _ _ _) ->
   (@body _ _ _ _ _ _ _ _) ->
   @body _ _ _ _ _ _ _ _ => idtac
end) | fail 1 "test_nat_goal failed : tower induction failed to produce the correct goal shape" ].

Goal forall (b : mon (nat -> nat -> Prop)) (c : Chain b),
elem c 4 5 -> elem c 5 6.
Fail tower induction. (* correct, [c] is not introduced yet *)
intros b c.
tower induction.
test_nat_goal.
Abort.

(** ** the primed tactics *)

Section s.

  (** on binary relations on natural numbers *)
  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (` R x y) (at level 80).
  Notation "x ≡ y" := (` _ x y) (at level 80).
  Notation "x [≡] y" := (b ` _ x y) (at level 80).
  Goal 5 ~ 6.
    coinduction' R H.
  Abort.
  Goal 5 ~ 6 /\ 7 ~ 8.
    coinduction' R H.
  Abort.
  Goal 5 ~ 6 /\ 7 ~ 8.
    coinduction' R _.
  Abort.
  Goal forall n, n+n ~ n+n.
    coinduction' R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m.
    coinduction' R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m /\ forall k, n+k ~ k+m.
    coinduction' R H.
  Abort.
  (* hypotheses mentioning [gfp b] are left untouched *)
  Goal gfp b 5 6 -> gfp b 7 8.
    coinduction' R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail coinduction' R H.
  Abort.


  Goal 5 ~ 6.
    coinduction' R H.
    cut (4 ≡[R] 5). admit.
    accumulate' H'.
    cut (3 ≡[R] 2). admit.
    accumulate' H''.
    cut ((forall x, x ≡[R] 1) /\ 0 ≡[R] 18). admit.
    accumulate' [H''' H''''].
  Abort.


  Notation b' := (cap s (converse ° s ° converse)).
  Goal forall n m, gfp b' n m.
  Proof.
    coinduction' R H.
    symmetric'.
  Abort.
  Goal forall n m, gfp b' (n+m) (m+n).
  Proof.
    coinduction' R H.
    symmetric'.
  Abort.
  Goal forall n m, gfp b' (n+m) (m+m).
  Proof.
    Fail symmetric'.
    coinduction' R H.
    Fail symmetric'.
    symmetric' using idtac.
    Fail default_sym_tac'.
  Abort.
  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall b, gfp b' (b+m) (n+b)).
    coinduction' R H.
    symmetric'.
  Abort.

End s.

(** support for heterogeneous relations of arbitrary arity *)
Section h.
  Variable b: mon (nat -> bool -> nat+bool -> unit -> Prop).

  Goal gfp b 4 true (inl 5) tt.
  Proof.
    coinduction' R H.
    cut (forall c, `R 3 c (inr c) tt). admit.
    accumulate' H'.
    cut (forall n, `R n false (inl n) tt). admit.
    accumulate' H''.
  Abort.
End h.

(** even dependent arities *)
Section h.
  Variable T: nat -> Type.
  Variable f: forall n, T n.
  Variable b: mon (forall n, T n -> T (n+n) -> Prop).

  Goal gfp b _ (f 2) (f 4).
  Proof.
    coinduction' R H.
    cut (forall n x, `R _ (f n) x). admit.
    accumulate' H'.
  Abort.
End h.

(** ** up-to bind *)

Section bind.

Context {T : Type -> Type}.
  Context {X Y X' Y': Type}.
Variable RR : X -> Y -> Prop.
Variable RR' : X' -> Y' -> Prop.

    Variable b : mon (forall (X Y : Type)
                   (RR' : X -> Y -> Prop) (x : T X) (y : T Y),
                   Prop
                   ).
  Variable bind : forall {A B} (a : T A) (k : A -> T B), T B.

  Lemma up_to_bind_gfp (x : T X) (y : T Y) (k1 : X -> T X') (k2 : Y -> T Y') :
    gfp b X Y RR x y ->
    (forall x' y', RR x' y' -> gfp b X' Y' RR' (k1 x') (k2 y')) ->
    gfp b X' Y' RR' (bind x k1) (bind y k2).
    coinduction' R H.
Abort.

  Lemma up_to_bind_chain (x : T X) (y : T Y) (k1 : X -> T X') (k2 : Y -> T Y')
  (c : Chain b)
  :
    elem c X Y RR x y ->
    (forall x' y', RR x' y' -> elem c X' Y' RR' (k1 x') (k2 y')) ->
    elem c X' Y' RR' (bind x k1) (bind y k2).
    tower induction.
Abort.

  Lemma up_to_bind_mixed_1 (x : T X) (y : T Y) (k1 : X -> T X') (k2 : Y -> T Y')
  (c : Chain b)
  :
    gfp b X Y RR x y ->
    (forall x' y', RR x' y' -> elem c X' Y' RR' (k1 x') (k2 y')) ->
    elem c X' Y' RR' (bind x k1) (bind y k2).
    tower induction.
Abort.


  Lemma up_to_bind_mixed_2 (x : T X) (y : T Y) (k1 : X -> T X') (k2 : Y -> T Y')
  (c : Chain b)
  :
    elem c X Y RR x y ->
    (forall x' y', RR x' y' -> gfp b X' Y' RR' (k1 x') (k2 y')) ->
    elem c X' Y' RR' (bind x k1) (bind y k2).
    tower induction.
Abort.
End bind.

(** ** symmetry arguments on a chain candidate *)

Section symmetry_tests.

Context {bnat : mon (nat -> nat -> Prop)}.
Notation bnat' := (cap bnat (converse ° bnat ° converse)).

Goal forall {R : Chain bnat'}
(Hsymmetric_holds : forall x y, bnat (elem R) (x+y) y /\ bnat (elem R) x y),
 forall x y,
bnat' (elem R) (x+y) y /\ bnat' (elem R) x y.
  intros R Hsymmetric_holds.
  begin_symmetry R.
  typeclasses eauto.
  monauto.
  icauto.
  intro P; revert_last;
  cbn [body converse]; clear; firstorder.
  exact Hsymmetric_holds.
Qed.

Goal forall {R : Chain bnat'}
(Hsymmetric_holds : forall x y, bnat (elem R) (x+y) y /\ bnat (elem R) x y),
 forall x y,
bnat' (elem R) (x+y) y /\ bnat' (elem R) x y.
  intros R Hsymmetric_holds.
  symmetric'.
  exact Hsymmetric_holds.
Qed.

End symmetry_tests.

(** [symmetric' R] acts on the [R] it is given, so supplying a candidate whose
    chain does not appear in the goal must fail *)
Section wrong_candidate.

  Variables s1 s2: mon (nat -> nat -> Prop).
  Notation b1 := (cap s1 (converse ° s1 ° converse)).
  Notation b2 := (cap s2 (converse ° s2 ° converse)).

  Goal forall (R1 : Chain b1) (R2 : Chain b2) n m, b1 (elem R1) n m.
    intros R1 R2 n m.
    Fail symmetric' R2 using idtac.
    symmetric' R1 using idtac.
  Abort.

End wrong_candidate.

(** ** the same tests, on the old (reification-based) tactics *)

Section s.

  (** on binary relations on natural numbers *)
  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (` R x y) (at level 80).
  Notation "x ≡ y" := (` _ x y) (at level 80).
  Notation "x [≡] y" := (b ` _ x y) (at level 80).
  Goal 5 ~ 6.
    coinduction R H.
    (* Restart.
    coinduction R _. *)
  Abort.
  Goal 5 ~ 6 /\ 7 ~ 8.
    coinduction R H.
    (* Restart.
    coinduction R [H H']. *)
  Abort.
  Goal forall n, n+n ~ n+n.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m.
    coinduction R H.
  Abort.
  Goal forall n m (k: n=m), n+n ~ m+m /\ forall k, n+k ~ k+m.
    coinduction R H.
  Abort.
  (* hypotheses mentioning [gfp b] are left untouched *)
  Goal gfp b 5 6 -> gfp b 7 8.
    coinduction R H.
  Abort.
  Goal gfp b 5 6 /\ gfp c 7 8.
    Fail coinduction R H.
  Abort.


  Goal 5 ~ 6.
    coinduction R H.
    cut (4 ≡[R] 5). admit.
    accumulate H'.
    cut (3 ≡[R] 2). admit.
    accumulate H''.
    cut ((forall x, x ≡[R] 1) /\ 0 ≡[R] 18). admit.
    accumulate [H''' H''''].
  Abort.


  Notation b' := (cap s (converse ° s ° converse)).
  Goal forall n m, gfp b' n m.
  Proof.
    coinduction R H.
    (* intros.  *)
    symmetric using idtac.
  Abort.
  Goal forall n m, gfp b' (n+m) (m+n).
  Proof.
    coinduction R H.
    symmetric.
  Abort.
  Goal forall n m, gfp b' (n+m) (m+m).
  Proof.
    Fail symmetric.
    coinduction R H.
    Fail symmetric.             
    symmetric using idtac.
    Fail default_sym_tac.
  Abort.
  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall b, gfp b' (b+m) (n+b)).
    coinduction R H.
    symmetric.
  Abort.

End s.
