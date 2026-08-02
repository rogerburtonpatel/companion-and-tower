(** * A genuinely ACTIVE-ONLY up-to technique, and its use in a proof.

    Setting: a transition system with
    - a PASSIVE step [pstep], which is total and deterministic (every state has
      exactly one), and
    - an ACTIVE step relation [qstep], arbitrary.

    [bp] is the passive behaviour (match the p-step), [bq] the active one
    (match q-steps).  The technique is

      [upto_pstep S  =  S  u  {(pstep u, pstep v) | S u v}]      ("up to one passive step")

    i.e. a pair may be justified by being one passive step ahead of a known
    pair.  We show:

    - [upto_pstep_below_w]: it is a sound ACTIVE technique ([<= w]).  Its active
      law genuinely consumes the diacritical premise [R <= bp R]: knowing the
      candidate already matches passive steps is exactly what turns "one step
      ahead of an [R]-pair" back into an [R]-pair.
    - [upto_pstep_not_ordinary]: it is NOT a sound ordinary up-to technique
      ([not <= t (bp cap bq)]) -- a concrete six-state counterexample.

    So this is the phenomenon the diacritical companion exists for: a technique
    usable in active position and unsound in passive position.

    Two further results:

    - [C0_D0_chain] uses an active-only technique INSIDE an ordinary
      [coinduction] proof, via the guarded behaviour [experiments.b_uw]: the
      passive conjunct of the goal offers [u], the active conjunct offers [w],
      so the position in the goal decides which techniques are legitimate.
    - [upto_pstep_strict] is a technique for which the TOWER route is
      NECESSARY: it is certified by [experiments.f_below_w_cup]
      ([upto_pstep_strict_below_w]), while the compatibility-style active law
      that [f_below_w_b] would need is outright false
      ([upto_pstep_strict_no_plain_active]). *)

From Stdlib Require Import Utf8 Setoid Morphisms.
Require Import lattice progress evolution companion diacritical_companion tower.
Require Import tactics utils.
Require Import experiments.

(* ------------------------------------------------------------------------- *)
(** ** The abstract setting and the technique *)

Section abstract.
Context {A : Type} (pstep : A -> A) (qstep : A -> A -> Prop).
Notation Rel := (A -> A -> Prop).

(* passive behaviour: the p-step is total and deterministic, so matching it is
   just "the p-successors are related" *)
Program Definition bp : mon Rel := {| body S := fun u v => S (pstep u) (pstep v) |}.
Next Obligation. intros S S' H u v Huv. now apply H. Qed.

(* active behaviour: every q-step of the left must be matched by the right *)
Program Definition bq : mon Rel :=
  {| body S := fun u v => forall u', qstep u u' -> exists2 v', qstep v v' & S u' v' |}.
Next Obligation.
  intros S S' H u v Huv u' Hu'. destruct (Huv u' Hu') as [v' Hq HS].
  exists v'; [ exact Hq | now apply H ].
Qed.

(* the technique: a pair counts if it is one passive step ahead of a known pair *)
Program Definition upto_pstep : mon Rel :=
  {| body S := fun x y => S x y \/ exists u v, S u v /\ x = pstep u /\ y = pstep v |}.
Next Obligation.
  intros S S' H x y [Hxy | [u [v [HS [-> ->]]]]].
  - left. now apply H.
  - right. exists u, v. split; [ now apply H | split; reflexivity ].
Qed.

#[local] Instance Pp : Progress (progress_mon bp) := progress_mono bp.
#[local] Instance Pq : Progress (progress_mon bq) := progress_mono bq.

Notation compan := (diacritical_companion.compan (progress_mon bp) (progress_mon bq)).
Notation u := (fst compan).
Notation w := (snd compan).
Notation b' := (cap bp bq).

(* PASSIVE law, unconditional.  Advancing an [S]-pair by one p-step lands in
   [upto_pstep S] by construction, which is what makes this hold. *)
Lemma upto_pstep_passive :
  forall R S : Rel, R <= bp S -> upto_pstep R <= bp (upto_pstep S).
Proof.
  intros R S H x y [Hxy | [m [n [HR [-> ->]]]]].
  - left. exact (H x y Hxy).
  - right. exists (pstep m), (pstep n).
    split; [ exact (H m n HR) | split; reflexivity ].
Qed.

(* ACTIVE law, CONDITIONAL.  The premise [R <= bp R] is used exactly once, and
   is indispensable: it converts the witness pair [(m,n)] into the pair
   [(pstep m, pstep n)] we are actually looking at, after which the active
   hypothesis applies directly. *)
Lemma upto_pstep_active :
  forall R S : Rel, R <= bp R -> R <= bq S -> upto_pstep R <= bq (upto_pstep S).
Proof.
  intros R S Hpre H x y [Hxy | [m [n [HR [-> ->]]]]].
  - intros x' Hq. destruct (H x y Hxy x' Hq) as [y' Hq' HS].
    exists y'; [ exact Hq' | now left ].
  - (* HERE is the diacritical premise at work *)
    assert (HR' : R (pstep m) (pstep n)) by exact (Hpre m n HR).
    intros x' Hq. destruct (H _ _ HR' x' Hq) as [y' Hq' HS].
    exists y'; [ exact Hq' | now left ].
Qed.

(* ---- a technique that NEEDS the tower ----

   [upto_pstep_strict] is [upto_pstep] with the [S] summand dropped: it returns
   ONLY shifted pairs.  It is therefore NOT inflationary ([f S] does not contain
   [S]), and that is exactly what breaks the compatibility-style proof: in the
   active law the q-obligations of a shifted pair land back in [S], and [f S]
   need not contain [S].  The tower target [snd x S] does contain it
   ([id_below_snd_chain]), so [f_below_w_cup] goes through. *)
Program Definition upto_pstep_strict : mon Rel :=
  {| body S := fun x y => exists m n, S m n /\ x = pstep m /\ y = pstep n |}.
Next Obligation.
  intros S S' H x y [m [n [HS [-> ->]]]]. exists m, n.
  split; [ now apply H | split; reflexivity ].
Qed.

Lemma upto_pstep_strict_passive :
  forall R S : Rel, R <= bp S -> upto_pstep_strict R <= bp (cup (upto_pstep_strict S) S).
Proof.
  intros R S H x y [m [n [HR [-> ->]]]].
  left. exists (pstep m), (pstep n).
  split; [ exact (H m n HR) | split; reflexivity ].
Qed.

Lemma upto_pstep_strict_active :
  forall R S : Rel, R <= bp R -> R <= bq S ->
    upto_pstep_strict R <= bq (cup (upto_pstep_strict S) S).
Proof.
  intros R S Hpre H x y [m [n [HR [-> ->]]]].
  (* the diacritical premise turns the witness into the pair we are looking at *)
  assert (HR' : R (pstep m) (pstep n)) by exact (Hpre m n HR).
  intros x' Hq. destruct (H _ _ HR' x' Hq) as [y' Hq' HS].
  (* the obligation lands in [S] -- available only because the target is a
     chain element, not [f S] *)
  exists y'; [ exact Hq' | now right ].
Qed.

Theorem upto_pstep_strict_below_w : upto_pstep_strict <= w.
Proof.
  apply (experiments.f_below_w_cup bp bq).
  - exact upto_pstep_strict_passive.
  - exact upto_pstep_strict_active.
Qed.

(* hence a sound ACTIVE up-to technique -- proved through the TOWER, in the
   chain-native style: [leq_w_chain] turns "[<= w]" into "below the active
   component of every chain element", [leq_w_chain_ind] is the tower induction,
   and [leq_snd_B_di] is the one-step obligation, stated in [bp]/[bq] only.
   The induction hypothesis [IH : upto_pstep <= snd x] is what lifts each law
   from target [upto_pstep S] to target [snd x S]. *)
Theorem upto_pstep_below_w : upto_pstep <= w.
Proof.
  di_upto x IH.
  - intros R S H. transitivity (bp (upto_pstep S)).
    + exact (upto_pstep_passive R S H).
    + apply bp, (IH S).
  - intros R S Hpre H. transitivity (bq (upto_pstep S)).
    + exact (upto_pstep_active R S Hpre H).
    + apply bq, (IH S).
Qed.

End abstract.

(* ------------------------------------------------------------------------- *)
(** ** It is NOT an ordinary up-to technique: a six-state counterexample.

    Two chains of passive steps.  On the [A] side the middle state has a q-step;
    on the [B] side it does not.  So [A0] and [B0] are NOT bisimilar.  Yet the
    singleton [{(A0,B0)}] progresses into [upto_pstep] of itself: its passive
    obligation is discharged by the "one step ahead" clause, and its active
    obligation is vacuous because [A0] itself has no q-step.  Using the
    technique in PASSIVE position is therefore unsound. *)

Inductive st := A0 | A1 | A2 | B0 | B1 | B2.

Definition ps (s : st) : st :=
  match s with
  | A0 => A1 | A1 => A2 | A2 => A2
  | B0 => B1 | B1 => B2 | B2 => B2
  end.

(* the only active step in the system *)
Inductive qs : st -> st -> Prop := q_A1 : qs A1 A2.

Notation bp' := (bp ps).
Notation bq' := (bq qs).
Notation bb  := (cap bp' bq').

Definition Rbad : st -> st -> Prop := fun x y => x = A0 /\ y = B0.

(* [Rbad] progresses -- in BOTH components -- into [upto_pstep Rbad] *)
Lemma Rbad_progress : Rbad <= bb (upto_pstep ps Rbad).
Proof.
  intros x y [-> ->]. split.
  - (* passive: [(A1,B1)] is one p-step ahead of [(A0,B0)] *)
    right. exists A0, B0. split; [ split; reflexivity | split; reflexivity ].
  - (* active: [A0] has no q-step *)
    intros x' Hq. inversion Hq.
Qed.

(* but [A0] and [B0] are not bisimilar *)
Lemma Rbad_not_gfp : ~ gfp bb A0 B0.
Proof.
  intro H.
  apply (gfp_pfp bb) in H. destruct H as [Hp _].
  cbn in Hp. (* gfp bb A1 B1 *)
  apply (gfp_pfp bb) in Hp. destruct Hp as [_ Hq].
  destruct (Hq A2 q_A1) as [v' Hqv _]. inversion Hqv.
Qed.

(* hence the technique is unsound as an ORDINARY up-to technique *)
Theorem upto_pstep_not_ordinary : ~ (upto_pstep ps <= companion.t bb).
Proof.
  intro H.
  (* if it were ordinary, [Rbad] would be a bt-post-fixpoint, hence bisimilar *)
  assert (Hsub : Rbad <= companion.gfp bb).
  { apply (coinduction bb Rbad). intros x y Hxy.
    apply (Hbody bb (upto_pstep ps Rbad) (companion.t bb Rbad) (H Rbad) x y).
    exact (Rbad_progress x y Hxy). }
  apply Rbad_not_gfp.
  pose proof (chain.gfp_tower bb) as E. apply weq_spec in E. destruct E as [E1 _].
  apply (E1 A0 B0). apply Hsub. split; reflexivity.
Qed.


(* ------------------------------------------------------------------------- *)
(** ** USE CASE: a coinductive proof whose ACTIVE obligation is discharged by
       [upto_pstep].

    Two states [C0], [D0] that each take one q-step, into their own passive
    successors, and then loop.  We prove them bisimilar from the SINGLETON
    candidate [{(C0,D0)}].  The two obligations are discharged by different
    techniques, which is the whole point:

    - PASSIVE, with [const di_similarity] (a legitimate passive technique,
      [disim_const_below_ucompan]): the p-successors [C1], [D1] are already
      bisimilar.
    - ACTIVE, with [upto_pstep] (legitimate ONLY here, by
      [upto_pstep_below_w]): the q-step lands on [(C1,D1)], which is not in the
      candidate but IS one passive step ahead of it.

    Discharging the ACTIVE obligation this way is sound; discharging a PASSIVE
    obligation the same way is not -- that is exactly
    [upto_pstep_not_ordinary]. *)

Inductive st2 := C0 | C1 | D0 | D1.

Definition ps2 (s : st2) : st2 :=
  match s with C0 => C1 | C1 => C1 | D0 => D1 | D1 => D1 end.

Inductive qs2 : st2 -> st2 -> Prop :=
| q_C0 : qs2 C0 C1
| q_D0 : qs2 D0 D1.

Notation P2 := (bp ps2).
Notation Q2 := (bq qs2).
Notation dis2 := (di_similarity (progress_mon P2) (progress_mon Q2)).

#[local] Instance Pp2 : Progress (progress_mon P2) := progress_mono P2.
#[local] Instance Pq2 : Progress (progress_mon Q2) := progress_mono Q2.

(* the tails are bisimilar: both loop and neither has a q-step *)
Lemma C1_D1 : dis2 C1 D1.
Proof.
  assert (H : (fun x y => x = C1 /\ y = D1) <= dis2).
  { apply leq_xsup. split.
    - intros x y [-> ->]. split; reflexivity.
    - intros x y [-> ->] x' Hq. inversion Hq. }
  apply H. split; reflexivity.
Qed.

(* the headline: proved from the SINGLETON candidate, using [upto_pstep] in the
   active position *)
Theorem C0_D0 : dis2 C0 D0.
Proof.
  assert (H : (fun x y => x = C0 /\ y = D0) <= dis2).
  { apply (soundness_f (progress_mon P2) (progress_mon Q2)
                       (const dis2) (upto_pstep ps2)).
    - (* PASSIVE: p-successors are already bisimilar *)
      intros x y [-> ->]. exact C1_D1.
    - (* ACTIVE: the q-target is one passive step ahead of the candidate --
         this is the step that needs an active-only technique *)
      intros x y [-> ->] x' Hq. inversion Hq; subst.
      exists D1; [ exact q_D0 | ].
      (* [(C1,D1)] is NOT in the candidate, but is one passive step ahead of it *)
      right. exists C0, D0. split; [ split; reflexivity | split; reflexivity ].
    - (* both techniques are legitimate in their own position *)
      split.
      + apply (disim_const_below_ucompan (progress_mon P2) (progress_mon Q2)).
      + apply (upto_pstep_below_w ps2 qs2). }
  apply H. split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** THE BRIDGE IN USE: the same result via [coinduction] on [b_uw].

    Compare [C0_D0] above, which had to name the candidate and both techniques
    in a [soundness_f] application.  Here we use the library's ordinary
    [coinduction] tactic on the guarded behaviour [b_uw], and the two conjuncts
    of the resulting goal hand us [u] passively and [w] actively. *)

Notation BB2 := (cap P2 Q2).
Notation UW2 := (b_uw P2 Q2).

(* register the technique once; resolution finds it from here on *)
#[local] Instance upto_pstep_active_inst : ActiveUpto P2 Q2 (upto_pstep ps2) :=
  upto_pstep_below_w ps2 qs2.

Theorem C0_D0_chain : gfp BB2 C0 D0.
Proof.
  di_coinduction R H.
  split.
  - (* PASSIVE conjunct: goal [u `R C1 D1].  Only passive techniques are on
       offer here; we use [const di_similarity <= u] and the fact that the
       p-successors are already bisimilar. *)
    bisim_passive R. exact C1_D1.
  - (* ACTIVE conjunct: goal [Q2 (w `R) C0 D0].  Here [w] is on offer, so the
       ACTIVE-ONLY technique applies -- at a chain element. *)
    intros x' Hq. inversion Hq; subst.
    exists D1; [ exact q_D0 | ].
    active_by (upto_pstep ps2) R.
    right. exists C0, D0. split; [ exact H | split; reflexivity ].
Qed.

(* ------------------------------------------------------------------------- *)
(** ** The tower is NECESSARY for [upto_pstep_strict], not just convenient.

    [f_below_w_b] would require the active law with target [f S]:
      [forall R S, R <= bp R -> R <= bq S -> f R <= bq (f S)]
    That statement is FALSE for [upto_pstep_strict].  Witness: two parallel
    chains of four states, with a single q-step in the middle of each.  The
    candidate [R] is the diagonal, [S] records only the q-target pair, and the
    shifted pair [(E1,F1)] has a q-obligation landing on [(E2,F2)] -- which is
    in [S] but not in [f S], because [f S] holds only the SHIFT of [S]. *)

Inductive st3 := E0 | E1 | E2 | E3 | F0 | F1 | F2 | F3.

Definition ps3 (s : st3) : st3 :=
  match s with
  | E0 => E1 | E1 => E2 | E2 => E3 | E3 => E3
  | F0 => F1 | F1 => F2 | F2 => F3 | F3 => F3
  end.

Inductive qs3 : st3 -> st3 -> Prop :=
| q_E1 : qs3 E1 E2
| q_F1 : qs3 F1 F2.

Definition R3 : st3 -> st3 -> Prop := fun x y =>
  (x = E0 /\ y = F0) \/ (x = E1 /\ y = F1) \/
  (x = E2 /\ y = F2) \/ (x = E3 /\ y = F3).
Definition S3 : st3 -> st3 -> Prop := fun x y => x = E2 /\ y = F2.

Lemma R3_passive : R3 <= bp ps3 R3.
Proof.
  intros x y [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]; cbn.
  - right; left; split; reflexivity.
  - right; right; left; split; reflexivity.
  - right; right; right; split; reflexivity.
  - right; right; right; split; reflexivity.
Qed.

Lemma R3_active : R3 <= bq qs3 S3.
Proof.
  intros x y [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]] x' Hq; inversion Hq; subst.
  exists F2; [ exact q_F1 | split; reflexivity ].
Qed.

(* the compatibility-style ACTIVE law fails *)
Theorem upto_pstep_strict_no_plain_active :
  ~ (forall R S : st3 -> st3 -> Prop,
        R <= bp ps3 R -> R <= bq qs3 S ->
        upto_pstep_strict ps3 R <= bq qs3 (upto_pstep_strict ps3 S)).
Proof.
  intro H.
  assert (Hpair : upto_pstep_strict ps3 R3 E1 F1).
  { exists E0, F0. split; [ left; split; reflexivity | split; reflexivity ]. }
  destruct (H R3 S3 R3_passive R3_active E1 F1 Hpair E2 q_E1) as [v' Hq HfS].
  (* [v'] must be [F2], and [f S3] holds only the SHIFT of [(E2,F2)] *)
  inversion Hq; subst.
  destruct HfS as [m [n [[-> ->] [Heq _]]]]. discriminate Heq.
Qed.
