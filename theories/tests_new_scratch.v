(** scratch for side-by-side goal states of old tactic vs primed tactic.
    I used this by compiling and diffing the OLD/NEW blocks. 
    not part of the build. *)
Require Import all.
Require Import infclosed.
Import CoindNotations.

Section s.
  Variables b c s: mon (nat -> nat -> Prop).
  Infix "~" := (gfp b) (at level 80).
  Notation "x ≡[ R ] y" := (` R x y) (at level 80).

  Goal 5 ~ 6.
    idtac "@@@ 1 OLD coinduction". coinduction R H. Show. Abort.
  Goal 5 ~ 6.
    idtac "@@@ 1 NEW coinduction'". coinduction' R H. Show. Abort.

  Goal 5 ~ 6 /\ 7 ~ 8.
    idtac "@@@ 2 OLD coinduction". coinduction R H. Show. Abort.
  Goal 5 ~ 6 /\ 7 ~ 8.
    idtac "@@@ 2 NEW coinduction'". coinduction' R H. Show. Abort.

  Goal forall n, n+n ~ n+n.
    idtac "@@@ 3 OLD coinduction". coinduction R H. Show. Abort.
  Goal forall n, n+n ~ n+n.
    idtac "@@@ 3 NEW coinduction'". coinduction' R H. Show. Abort.

  Goal forall n m (k: n=m), n+n ~ m+m.
    idtac "@@@ 4 OLD coinduction". coinduction R H. Show. Abort.
  Goal forall n m (k: n=m), n+n ~ m+m.
    idtac "@@@ 4 NEW coinduction'". coinduction' R H. Show. Abort.

  Goal forall n m (k: n=m), n+n ~ m+m /\ forall j, n+j ~ j+m.
    idtac "@@@ 5 OLD coinduction". coinduction R H. Show. Abort.
  Goal forall n m (k: n=m), n+n ~ m+m /\ forall j, n+j ~ j+m.
    idtac "@@@ 5 NEW coinduction'". coinduction' R H. Show. Abort.

  Goal gfp b 5 6 -> gfp b 7 8.
    idtac "@@@ 6 OLD coinduction". coinduction R H. Show. Abort.
  Goal gfp b 5 6 -> gfp b 7 8.
    idtac "@@@ 6 NEW coinduction'". coinduction' R H. Show. Abort.

  (* accumulation *)
  Goal 5 ~ 6.
    coinduction R H.
    cut (4 ≡[R] 5). admit.
    idtac "@@@ 7 OLD accumulate #1". accumulate H'. Show.
    cut (3 ≡[R] 2). admit.
    idtac "@@@ 7 OLD accumulate #2". accumulate H''. Show.
    cut ((forall x, x ≡[R] 1) /\ 0 ≡[R] 18). admit.
    idtac "@@@ 7 OLD accumulate #3". accumulate [H''' H'''']. Show.
  Abort.
  Goal 5 ~ 6.
    coinduction' R H.
    cut (4 ≡[R] 5). admit.
    idtac "@@@ 7 NEW accumulate' #1". accumulate' H'. Show.
    cut (3 ≡[R] 2). admit.
    idtac "@@@ 7 NEW accumulate' #2". accumulate' H''. Show.
    cut ((forall x, x ≡[R] 1) /\ 0 ≡[R] 18). admit.
    idtac "@@@ 7 NEW accumulate' #3". accumulate' [H''' H'''']. Show.
  Abort.

  (* symmetry *)
  Notation b' := (cap s (converse ° s ° converse)).
  Goal forall n m, gfp b' n m.
    coinduction R H. idtac "@@@ 8 OLD symmetric". symmetric. Show. Abort.
  Goal forall n m, gfp b' n m.
    coinduction' R H. idtac "@@@ 8 NEW symmetric'". symmetric'. Show. Abort.

  Goal forall n m, gfp b' (n+m) (m+n).
    coinduction R H. idtac "@@@ 9 OLD symmetric". symmetric. Show. Abort.
  Goal forall n m, gfp b' (n+m) (m+n).
    coinduction' R H. idtac "@@@ 9 NEW symmetric'". symmetric'. Show. Abort.

  Goal forall n m, gfp b' (n+m) (m+m).
    coinduction R H. idtac "@@@ 10 OLD symmetric using idtac". symmetric using idtac. Show. Abort.
  Goal forall n m, gfp b' (n+m) (m+m).
    coinduction' R H. idtac "@@@ 10 NEW symmetric' using idtac". symmetric' using idtac. Show. Abort.

  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall j, gfp b' (j+m) (n+j)).
    coinduction R H. idtac "@@@ 11 OLD symmetric". symmetric. Show. Abort.
  Goal forall n m, (forall a, gfp b' (n+a) (a+m)) /\ (forall j, gfp b' (j+m) (n+j)).
    coinduction' R H. idtac "@@@ 11 NEW symmetric'". symmetric'. Show. Abort.
End s.

(** dependent arities: where binder loss was worst *)
Section h.
  Variable T: nat -> Type.
  Variable f: forall n, T n.
  Variable b: mon (forall n, T n -> T (n+n) -> Prop).

  Goal gfp b _ (f 2) (f 4).
    idtac "@@@ 12 OLD coinduction". coinduction R H. Show.
    cut (forall n x, `R _ (f n) x). admit.
    assert (`R _ (f 1) (f 2)) by admit.
    idtac "@@@ 12 OLD accumulate". accumulate H'. Show.
  Abort.
  Goal gfp b _ (f 2) (f 4).
    idtac "@@@ 12 NEW coinduction'". coinduction' R H. Show.
    cut (forall n x, `R _ (f n) x). admit.
    assert (`R _ (f 1) (f 2)) by admit.
    idtac "@@@ 12 NEW accumulate'". accumulate' H'. Show.
  Abort.
End h.
