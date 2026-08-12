(** * Automatically discharge [inf_closed] side conditions 

    [tower] requires [inf_closed P] for the predicate [P] one reasons about.
    Rather than reifying the goal so that [P] always has a fixed shape, we
    observe that inf-closedness is compositional over the syntax of [P], and let
    [auto] follow that syntax.

    The driver for this is the indexed reformulation [inf_closed'] below. It
    composes definitionally, since 
    [inf' Q f a] 
    is by definition 
    [inf' Q (fun i => f i a)] 
    in the lattice of (dependent) functions. 
    
    In particular the base case, 
    aka the goal mentioning the candidate applied to arguments, 
    needs no particular lemmas at any arity, because 
    after peeling the arguments the goal is exactly the hypothesis.
 *)

Require Export lattice tower rel.
Set Implicit Arguments.


Lemma inf_closed_and {X} {L: CompleteLattice X} (P Q: X -> Prop):
  inf_closed P -> inf_closed Q -> inf_closed (fun x => P x /\ Q x).
Proof. apply inf_closed_cap. Qed. 

(** ** structural lemmas for monotonicity *)

Lemma all_mono {X} {L: CompleteLattice X} A (P: A -> X -> Prop):
  (forall a, Proper (leq ==> leq) (P a)) ->
  Proper (leq ==> leq) (fun x => forall a, P a x).
Proof. intros H x y xy Hx a. now apply (H a x y xy). Qed.

Lemma and_mono {X} {L: CompleteLattice X} (P Q: X -> Prop):
  Proper (leq ==> leq) P -> Proper (leq ==> leq) Q ->
  Proper (leq ==> leq) (fun x => P x /\ Q x).
Proof.
  intros HP HQ x y xy []. split.
  now apply (HP x y xy). now apply (HQ x y xy).
Qed.

(** through a monotone function applied to the candidate, as in [b R u v] *)
Lemma body_mono {X} {L: CompleteLattice X} (b: mon X) (P: X -> Prop):
  Proper (leq ==> leq) P -> Proper (leq ==> leq) (fun x => P (b x)).
Proof. intros HP x y xy. apply HP. now apply b. Qed.

(** ** the automatic procedure *)

 
(* Todo move this *)
Create HintDb mon discriminated. 

#[export] Hint Resolve all_mono and_mono body_mono : mon. 
#[export] Hint Resolve mon_sup mon_inf mon_cup mon_cap : mon. 

#[export] Hint Extern 2 (Proper (leq ==> leq) _) =>
  (solve [repeat intro; match goal with H: _ <= _ |- _ => apply H; assumption end]) : mon.

Create HintDb ic discriminated.
#[export] Hint Resolve inf_closed_all 
                       inf_closed_cap 
                       inf_closed_and 
                       inf_closed_leq 
                       inf_closed_impl : ic.

(** base cases: the candidate applied to arguments. *)
#[export] Hint Extern 2 (inf_closed _) =>
  (solve [intros ? ?; assumption]) : ic.

(** [solve_ic] attempts to solve a goal of the form [inf_closed P] for a 
    predicate P. 
    If it cannot, it reports the shape it got stuck on 
    so that debugging is bearable. *)
Ltac solve_ic :=
  (* apply inf_closed'_inf_closed; *)
  tryif solve [auto 20 with ic mon nocore] then idtac
  else match goal with
       (* | |- inf_closed' ?P => *)
       | |- inf_closed ?P =>
         fail 1 "[coinduction] cannot show that this predicate is inf-closed:" P
       | _ => fail 1 "bug in solve_ic, please report"
       end.
Goal inf_closed (fun P : nat -> bool -> nat + bool -> unit -> Prop => P 4 true (inl 5) tt). 
  solve_ic.
Qed.  

Section h.
  Variable T: nat -> Type.
  Variable f: forall n, T n.
  Variable b: mon (forall n, T n -> T (n+n) -> Prop).

Goal inf_closed (fun P : forall n : nat, T n -> T (n + n) -> Prop => P 2 (f 2) (f 4)).
  solve_ic. 
Qed.  
End h. 

(* tests for up to bind *)

(* apply inf_closed'_inf_closed.  *)
(** * Starting a proof by coinduction

    [apply tower] on its own cannot always guess the predicate [P] to induct on,
    even when there is only one instance of [elem] in the goal as when starting
    a proof by coinduction. If it guesses a wrong predicate shape which is not
    inf-closed, the proof will fail. 

    The previous reification machinery in [tactics.v] and [reification.ml]
    solved this by coercing the goal into a custom [pTs] data structure that
    could always be recognized as an inf-closed predicate and automatically
    discharging the first obligation that way. This can be done in Rocq, but
    recovering the original goal from the data structure resulted in the loss of
    the original bound names. Thus the library used an OCaml plugin to recover
    the names. 

    But a simpler, Rocq-native solution is desirable: it is more easily
    debuggable, and more durable. Several bugs in the OCaml plugin led to
    confusing error messages or unpredictable behavior, most notably the
    inability to perform coinduction on a goal of the form 

    [gfp b x y -> gfb b x y]

    as [gfp]-predicates in hypotheses were rejected, even when valid. 


    We now present a Rocq-native solution that simplifies the machinery, works
    in many fewer lines of code, fixes the bugs, and presents more descriptive
    error messages. 

    First, we observe an invariant: proofs by coinduction via tower induction
    always involve candidates of a single chain. This is because 'membership in
    the [gfp],' which is the goal of a coinductive proof, is necessarily the
    conclusion of the proof's type. Proof by tower induction proceeds by first
    stating the 'membership in the [gfp]' goal as a predicate [P] of _all_
    elements of the tower using [gfp_prop], and then proceeds by tower
    induction. 

    When using this technique, if the goal only mentions -> and /\, the
    predicate [P] is always inf-closed, so the first obligation of tower
    induction can automatically be dispatched. 

    TODO explain why. The short of it is that in the lattice of dependent
    functions into [Prop], logical connectives are inf-closed. 

    QUESTION: can we do better? existentials are the curiosity here... 



    Example: 

    [Lemma needs_coinduction : forall ... (H: ...), gfp b ....] 

    [Lemma does_not_need_coinduction : forall ... (H: gfp b ...), G].

    where [G] is a goal that does not mention [gfp b].

    Proof by coinduction via tower induction restate a goal involving the [gfp]
    as a property of _all_ elements of the tower using [gfp_prop]:

    forall (x : Chain b), forall ... (H: ...), P (elem x). (* TODO write this a
    bit more clearly *)

    and then apply [ptower] to prove the property holds of all elements. 

    Goal 1: inf_closed P 
    Goal 2: P (elem x) -> P (b (elem x)). 

    Because of this, in this particular case, [pattern (elem R)] always performs
    the necessary abstraction, turning the goal into [?P (elem R)]
    syntactically. Then the application is first-order, and the inf-closedness
    of [P] can always be dispatched by a solver for [P] of the form...

    TODO MAKE THIS FORMAL. 

    Pous previously formalized this using a custom type that allowed only 
    names, conjunctions, and abstractions. We use a theorem of inf-closedness
    of firstorder logic. 

    TODO: does this exist? We have a series of lemmas for abstraction, 
    conjunction, dependent abstraction, and others. What else can we get? 

    Since [P] is then literally the original goal abstracted over the candidate,
    the names of all bound variables are preserved for free. This deprecates the
    need for reification machinery, which coerced the goal into a form that
    could automatically be solved 


    This is the sole reason the reification machinery exists: reducing [pT]
    instead would reset those names, because the binder in [pT (abs B Q) x =
    forall b, ...] comes from the definition of [pT] rather than from the user's
    goal, turning [forall n m j, ...] into [forall b0 b1 b2,
    ...].

    The [inf_closed] side condition is discharged by [solve_ic] above, which
    simply follows the syntax of [P]. *)

(** [gfp_prop] must only abstract the occurrences of [gfp b] sitting in the
    conclusion of the goal: those appearing in hypotheses are to be left alone,
    so that [coinduction] on [gfp b 5 6 -> gfp b 7 8] keeps the premise as
    [gfp b 5 6] rather than turning it into a statement about the candidate.
    We thus strip the leading telescope into the context before applying
    [gfp_prop], and revert it once [R] has been introduced.
    [intro] (rather than [intro h] on a fresh [h]) preserves binder names. *)
Ltac gfp_intro' R :=
  lazymatch goal with
  | |- forall _ : _, _ =>
      intro;
      lazymatch goal with
      | h: _ |- _ => gfp_intro' R; revert h
      end
  | |- _ => apply gfp_prop; intro R
  end.

Tactic Notation "coinduction'" ident(R) simple_intropattern(H) :=
  gfp_intro' R; pattern (elem R); revert R;
  apply tower; [ solve_ic | intro R; cbn beta; intros H ].

(* Tower induction *)

(* tower induction always leaves the goal with the form `forall _ : Chain, ...` ; 
   match on this type and clear the old Chain *) 
Ltac clear_old_chain := lazymatch goal with 
  | c : (Chain ?b) |- forall _ : (Chain ?b), _ => clear c; intro c end.

Ltac tower_induction_with c := 
    pattern (elem c);
    apply tower;
    [solve_ic | try clear_old_chain]. 

Tactic Notation "tower" "induction" "with" ident(c) := tower_induction_with c. 

Ltac tower_induction := 
lazymatch goal with 
  | c : Chain _ |- _ => 
    (* catch : more than one chain *)
    (lazymatch goal with 
      (* two chains means we cannot guess the candidate, it must be supplied manually *)
      | c1 : Chain _, c2 : Chain _ |- _ => 
        fail 1 "[coinduction]: found more than one chain candidate (found" c1 " and " c2 ")."
              "Supply the candidate manually using `tower_induction_with [c]`"
      | _ => tower_induction_with c
      end)
  | _ => (* no chain *) fail 1 "[coinduction]: no Chain candidate found. tower induction
                                reqires a context element of type `Chain _`"
  end. 

Tactic Notation "tower" "induction" := tower_induction.


(* tests for tower induction *)

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


(** * Accumulating, without reification

    To keep both the same chain and the correct hypothesis shapes, accumulation
    must use [tower.ptower] to separates a monotone hypothesis [Q] from the
    inf-closed conclusion [P]. In [Q] must be stored each existing hypothesis
    about [c] (the Chain) so that tower induction does not act upon it and
    transform it from (elem c) into [b (elem c)]. 

    As [Q] is a single predicate, the [n] hypotheses about the candidate have to
    be folded into one conjunction before applying it, and unfolded again
    afterwards. This is the responsibility of [and_curry]/[and_uncurry].
    *)

Lemma and_uncurry (A B C: Prop): (A /\ B -> C) -> (A -> B -> C).
Proof. tauto. Qed.
Lemma and_curry (A B C: Prop): (A -> B -> C) -> (A /\ B -> C).
Proof. tauto. Qed.

(** [n] is the number of foldings performed on the way in, i.e. one less than
        the number of hypotheses about [R]. [ptower] is then applied at [R]
        directly, and its step goal re-introduces the candidate: the old one is
        unused by this point, since every hypothesis mentioning it has been
        reverted. *)

(** undo [n] foldings.  the foldings nest to the right, so after splitting the
      outermost conjunction the next one sits under a binder. We use [refine]
      rather than [apply], which over-strips here and tries to match
      [and_curry]'s premise against the goal's domain. *)
Ltac uncurry_back n :=
  lazymatch n with
  | O => idtac
  | S ?m =>
      refine (and_curry _);
      let h := fresh "h" in intro h; uncurry_back m; revert h
  end.

Ltac apply_ptower' R n :=
  pattern (elem R);
  lazymatch goal with
  | |- (fun z => @?Q z -> @?P z) _ =>
      cbn beta;
      apply (ptower (Q:=Q) (P:=P));
      [ solve [auto 20 with ic mon nocore]
      | solve_ic
      | clear R; intro R; cbn beta; uncurry_back n ]
  | |- _ => fail 1 "[coinduction] no hypothesis about the candidate to accumulate"
  end.


(** revert every hypothesis mentioning [R], folding them into a single
    conjunction on the way in, and restoring them by their original names on
    the way out.  [xaccumulate0] handles the first one, which needs no folding. *)
Ltac xaccumulate1 R n :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; apply and_uncurry; xaccumulate1 R (S n); intro H
  | _ => apply_ptower' R n
  end.
Ltac xaccumulate0 R :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; xaccumulate1 R 0; intro H
  | _ => apply_ptower' R 0
  end.

Tactic Notation "accumulate'" hyp(R) simple_intropattern(H) :=
  xaccumulate0 R; intros H.
Tactic Notation "accumulate'" simple_intropattern(H) :=
  lazymatch goal with
  | R: Chain _ |- _ => accumulate' R H
  | _ => fail "could not find the coinductive candidate"
  end.



  (* up-to bind tests *)

Section bind. 

Context {T : Type -> Type}. 
  Context {X Y X' Y': Type}.
  (* {CLX : CompleteLattice X}
               {CLY : CompleteLattice Y}. *)
Variable RR : X -> Y -> Prop. 
Variable RR' : X' -> Y' -> Prop. 

    Variable b : mon (forall (X Y : Type) 
                   (RR' : X -> Y -> Prop) (x : T X) (y : T Y), 
                   Prop
                   ). 
  Variable bind : forall {A B} (a : T A) (k : A -> T B), T B. 

  Definition bisim : forall X Y RR, T X -> T Y -> Prop := gfp b. 

(* Ltac test_bind_goal := 
first [
  (lazymatch goal with 
|- (elem _ _ _ _ _ _ -> elem _ _ _ _ _) ->
   (@body  _ _ _ _ _ _ _ _ _ _ _) -> 
   @body _ _ _ _ _ _ _ _ _ _ _ => idtac
end) | fail 1 "test_bind_goal failed : tower induction failed to produce the correct goal shape" ]. *)


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
    (* test_bind_goal.   *)
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

