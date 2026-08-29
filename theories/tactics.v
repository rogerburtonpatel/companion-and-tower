(** * Tactics for coinductive n-ary relations *)

(**
we provide three tactics:
- [coinduction R H] to start a proof by coinduction 
  [R] is a name for the bisimulation candidate,
  [H] is an introduction pattern for the properties of the candidate
- [accumulate H] to accumulate new pairs in the bisimulation candidate
  [H] is an introduction pattern, as above
- [symmetric] to reason by symmetry when the coinductive (binary) relation is defined by a symmetric function.
  this tactics makes it possible to play only half of the coinductive game, provided it manages to prove automatically that the candidate is symmetric.
  A tactic [tac] for solving the symmetry requirement may be passed as follows:
  [symmetric using tac]
  (by default, we use solve[clear;firstorder])
*)


(** * Automatically discharge [inf_closed] side conditions

    [tower] requires [inf_closed P] for the predicate [P] one reasons about.
    Rather than reifying the goal so that [P] always has a fixed shape, we
    observe that inf-closedness is compositional over the syntax of [P], and let
    [auto] follow that syntax.

    In particular the base case, aka the goal mentioning the candidate applied
    to arguments, needs no particular lemmas at any arity, because after peeling
    the arguments the goal is exactly the hypothesis.
 *)


Require Export lattice tower rel.
Set Implicit Arguments.

(* the [mon] database TODO DOCUMENT. *)
Create HintDb mon discriminated.
#[global] Hint Resolve all_mono and_mono body_mono : mon.
#[global] Hint Resolve mon_sup mon_inf mon_cup mon_cap : mon.

#[global] Hint Extern 2 (Proper (leq ==> leq) _) =>
  (solve [repeat intro; match goal with H: _ <= _ |- _ => apply H; assumption end]) : mon.

(* todo make this bound less of a hack *)
(* this catches a particular corner case which is relevant in the study of
   active-only up-to techniques. 

   the corner case is a hypothesis in which the candidate sits under a monotone
   function it is not the chain of, as in [ba (elem c) u v] with [c : Chain b].
   that predicate is indeed monotone in the candidate, but [auto] cannot see it
   because using [body_mono] would mean reading [fun w => ba w u v] as [fun w =>
   Q (ba w)], and there is no first-order way to guess [Q]. so we peel the
   arguments off, then walk back out through each monotone function in turn
   using its own [Hbody]. we use [match] rather than [lazymatch] so nesting like
   [ba (b w)] can backtrack onto the inner function first. the bound stops the
   wrapping from looping. *)
Ltac mon_lift H n :=
  first [ solve [assumption | apply H; assumption]
        | lazymatch n with
          | S ?m =>
              match goal with
              | |- context [@body _ _ ?b _] => mon_lift (Hbody b _ _ H) m
              end
          end ].

#[global] Hint Extern 4 (Proper (leq ==> leq) _) =>
  (solve [ repeat intro;
           lazymatch goal with H : _ <= _ |- _ => mon_lift H 4 end ]) : mon.

Ltac apply_leq :=
  match goal with
  | [H: _ <= _ |- _] => intros; apply H
  | [H: leq _ _ |- _] => intros; apply H
  end.

Ltac induct_on_premise :=
  once (match reverse goal with
        | H: context [?rel _] |- context [?rel] => induction H
        end).

Ltac functor_mono :=
  solve [ cbv; intros;
          solve [ induct_on_premise; try econstructor; try apply_leq; eauto 5 ] ].

Ltac monauto :=
  solve [auto 20 with mon] ||
  functor_mono ||
   fail "`monauto` could not solve this goal.".


(** ** the automatic procedure *)

Create HintDb ic discriminated.
#[global] Hint Resolve inf_closed_all
                       inf_closed_cap
                       inf_closed_and
                       inf_closed_leq
                       inf_closed_impl : ic.

(** base cases: the candidate applied to arguments. *)
#[global] Hint Extern 2 (inf_closed _) =>
  (solve [intros ? ?; assumption]) : ic.

(** the relation classes, at any arity *)
#[global] Hint Extern 1 (inf_closed _) =>
  (progress (unfold Reflexive, Symmetric, Transitive, Proper, respectful,
                    iff, Basics.flip, Basics.impl)) : ic.

(** [icauto] attempts to solve a goal of the form [inf_closed P] for a
    predicate P.
    If it cannot, it reports the shape it got stuck on
    so that debugging is bearable. *)
Ltac icauto :=
  tryif solve [auto 20 with ic mon nocore] then idtac
  else match goal with
       | |- inf_closed ?P =>
         fail 1 "[coinduction] cannot show that this predicate is inf-closed:" P
       | _ => fail 1 "bug in icauto, please report"
       end.

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

    The [inf_closed] side condition is discharged by [icauto] above, which
    simply follows the syntax of [P]. *)

(** [gfp_prop] can abstract the [gfp] of only one function, so a conclusion
    mentioning two of them cannot be a proof by coinduction.  detect that here:
    otherwise the abstraction silently keeps the other [gfp] and the failure
    surfaces much later, as an inf-closedness goal that mentions it.
    [match] rather than [lazymatch] so that both occurrences are enumerated. *)
Ltac two_candidates :=
  match goal with
  | |- context [@gfp ?X ?L ?b1] =>
      match goal with
      | |- context [@gfp X L ?b2] => tryif unify b1 b2 then fail else idtac
      end
  end.

Ltac check_one_candidate :=
  tryif two_candidates then
    fail "[coinduction] only one coinductive candidate is allowed: this conclusion mentions the gfps of two different functions"
  else idtac.

(** [gfp_prop] must only abstract the occurrences of [gfp b] sitting in the
    conclusion of the goal: those appearing in hypotheses are to be left alone,
    so that [coinduction] on [gfp b 5 6 -> gfp b 7 8] keeps the premise as
    [gfp b 5 6] rather than turning it into a statement about the candidate.
    We thus strip the leading telescope into the context before applying
    [gfp_prop], and revert it once [R] has been introduced.
    [intro] (rather than [intro h] on a fresh [h]) preserves binder names.
    The candidate is introduced under a private name and renamed to [R] only
    once the telescope has been reverted, since the telescope may itself bind
    [R]. *)

(** the conclusion is often stated through a definition standing for the
    greatest fixpoint, as in [Definition eutt := gfp b]. [gfp] is opaque, so
    [repeat red] stops exactly when the fixpoint is exposed. Without this,
    [apply gfp_prop] unifies its [P gfp] against the folded conclusion by
    taking [P] constant, and the failure only surfaces later, as [pattern]
    finding no subterm. *)
Ltac expose_gfp :=
  lazymatch goal with
  | |- context [@gfp _ _ _] => idtac
  | |- _ =>
      tryif progress (repeat red) then expose_gfp
      else fail 1 "[coinduction] no greatest fixpoint in the conclusion"
  end.

Ltac gfp_intro_ c :=
  lazymatch goal with
  | |- forall _ : _, _ =>
      intro;
      lazymatch goal with
      | h: _ |- _ => gfp_intro_ c; revert h
      end
  | |- _ => expose_gfp; check_one_candidate; apply gfp_prop; intro c
  end.

Ltac gfp_intro' R :=
  let c := fresh "coind_candidate" in
  gfp_intro_ c;
  rename c into R.

(** ** starting a proof by (enhanced) coinduction *)
(** when the goal is of the shape

    [forall x y..., gfp b u v /\ forall z, P -> gfp b s t]

    where x,y... may appear in u, v, P, s, t and z may appear in P, s ,t
    (more complex alternations of quantifiers/conjunctions/implications being allowed)
    and [b] is the function for the considered coinductive relation

    [coinduction R H] moves to a goal

    R: Chain b
    H: forall x y..., `R u v /\ forall z, P -> `R s t
    -------------------------------------------------------
    forall x y..., b `R u v /\ forall z, P -> b `R s t

    [R] should be understood as the bisimulation up-to candidate.
    [H] expresses the pairs [R] is assumed to contain.
    Note the move to [b `R] in the conclusion: now we should play at least one step of the coinductive game for all pairs inserted in the candidate.
    Also note that [H] may be an introduction pattern.
 *)

Tactic Notation "coinduction" ident(R) simple_intropattern(H) :=
  gfp_intro' R; pattern (elem R); revert R;
  apply tower; [ icauto | intro R; cbn beta; intros H ].

(* Tower induction *)

(* tower induction always leaves the goal with the form `forall _ : Chain, ...` ;
   match on this type and clear the old Chain *)
Ltac clear_old_chain := lazymatch goal with
  | c : (Chain ?b) |- forall _ : (Chain ?b), _ => clear c; intro c end.

Ltac tower_induction_with c :=
    pattern (elem c);
    apply tower;
    [icauto | try clear_old_chain].

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
            directly, and its step goal re-introduces the candidate. the old
            candidate is unused by this point, since every hypothesis mentioning
            it has been reverted. *)

(** undo [n] foldings.  the foldings nest to the right, so after splitting the
        outermost conjunction the next one sits under a binder. We use [refine]
        rather than [apply], which over-strips. *)
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
      [ monauto
      | icauto
      | clear R; intro R; cbn beta; uncurry_back n ]
  | |- _ => fail 1 "[coinduction] no hypothesis about the candidate to accumulate"
  end.


(** revert every hypothesis mentioning [R], folding them into a single
    conjunction on the way in, and restoring them by their original names on
    the way out.  [xaccumulate0] handles the first one, which needs no folding. *)
Ltac xaccumulate1 R n :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; refine (and_uncurry _); xaccumulate1 R (S n); intro H
  | _ => apply_ptower' R n
  end.
Ltac xaccumulate0 R :=
  lazymatch goal with
  | H: context[R] |- _ => revert H; xaccumulate1 R 0; intro H
  | _ => apply_ptower' R 0
  end.

(** [accumulate] adds the conclusion to the candidate, so the conclusion must be
      built from the candidate itself ([elem c]), and conjunctions and
      quantifiers of those.  applying a function to it, as in [b (elem c)], is
      not something that can be assumed. we report that directly rather than
      letting it surface as a failed inf-closedness goal. a premise may mention
      the candidate under a function, but the conclusion may not. *)
Ltac check_accumulate_concl R :=
  tryif assert_succeeds
          (repeat lazymatch goal with |- forall _ : _, _ => intro end;
           lazymatch goal with
           | |- context [@body _ _ _ (elem R)] => idtac
           | |- context [@elem _ _ _ (@chain_b _ _ _ R)] => idtac
           end)
  then fail "[coinduction] accumulate expects a conclusion about the candidate itself, as in `elem c u v` (conjunctions and quantifiers are fine); this one applies a function to the candidate"
  else idtac.

(** ** accumulating knowledge in a proof by enhanced coinduction *)

(** when the goal is of the shape, typically obtained after starting a proof by coinduction and    performing one step of the coinductive game:

    R: Chain b
    H: forall x y, `R u v
    H': forall x y z, P -> `R s t
    --------------------------------
    forall i j, `R p q

    (more complex alternations of quantifiers/conjunctions/implications being allowed in both hypotheses and conclusion)

    [accumulate H''] moves to a goal

    R: Chain b
    H: forall x y, `R u v
    H': forall x y z, P -> `R s t
    H'': forall i j, `R p q
    --------------------------------
    forall i j, b `R p q

    The conclusion has been saved as an hypothesis [H''],
    and a [b] has been inserted in the conclusion, so that we have to play at least one step of the coinductive game on the added pairs

    Like for [coinduction], [H''] maybe an introduction pattern.
 *)

Tactic Notation "accumulate" hyp(R) simple_intropattern(H) :=
  check_accumulate_concl R; xaccumulate0 R; intros H.
Tactic Notation "accumulate" simple_intropattern(H) :=
  lazymatch goal with
  | R: Chain _ |- _ => accumulate R H
  | _ => fail "could not find the coinductive candidate"
  end.


(* symmetry arguments *)

(*
  symmetric needs to:
  apply a by_symmetry lemma which creates 3 goals:
  1 to find [s]
  1 to prove the 'symmetric shape' of the goal, ideally with names intact
  1 where [s] replaces [b], with names intact.
*)



(** the [b] used to recognise the application in the goal is read off the type
      of the supplied [R]. *)
Ltac begin_symmetry R :=
  lazymatch type of R with
  | @Chain _ _ ?b =>
      lazymatch goal with
      | |-context [@body ?X ?LX b ?x] =>
          pattern (@body X LX b x);
          eapply by_symmetry'
      | _ => fail "could not find an application of the coinductive function in the goal"
      end
  | _ => fail "could not find coinductive candidate of form `Chain _`"
  end.

Ltac _revert_last := match goal with
| H:_ |- _ => revert H
end. 

Ltac apply_by_symmetry R tac :=
  (* first, extract the predicate [P] to use default_sym_tac) *)
  begin_symmetry R;
  (* then the subgoals are: *)
  [
    (* 1. find [s], the Symmetrical converse of [b].
       Typeclass resolution will attempt this to find [s]
       automatically; if it cannot be found it must be proved.
       [once] is needed to ensure the right error messages are
       propagated upwards from later tactics. *)
  try once typeclasses eauto
  (* 2. [P] must be monotone. Here we use our user-facing
        solver that dispatches simple monotonicity proofs. *)
  | try auto with mon
  (* 3. [P] must be inf-closed. We do as in 2. *)
  | try icauto
  (* 4. [P] must have a symmetric shape. We do some tidying to first clean
        up the proof state:
        a. [intro P; _revert_last] simply puts the goal into a shape
        where prior names are preserved.
        b. [cbn [body converse]] does the symmetric 'flip' of the goal
            so it is obvious the user needs to prove symmetry of [P].
        then run the user-supplied [tac] to attempt
        to "get symmetry automatically." In particular, if the user
        supplies no tactic, [tac] will be [solve [clear; firstorder]].
        If they supply [idtac], the goal will remain untouched. *)
  | intro P; _revert_last; cbn [body converse]; tac
  (* 5. The remaining goal is for the user to solve: that the
        relation with [s] replacing [b]. We leave this goal untouched. *)
  |].


(* todo build to use ltac rather than notation, as notation is harder to find *)
Ltac default_sym_tac := solve [clear;firstorder] || fail "could not get symmetry automatically".
(** reasoning on symmetric candidates with symmetric functions *)
(** this tactic makes it possible to play only half of the coinductive game in cases where both the game and the current goal are symmetric:
    - that the game is symmetric is inferred using the typeclasse [Symmetrical]
    - that the goal is symmetric is proven using the given tactic (by default, [firstorder])
    the goal should be of the form
    [forall x y..., b `R u v] 
    it moves to a goal of the form
    [forall x y..., s `R u v] 
    (where [R: Chain b] with [b] the function for the coinductive game, and [s] the function for the `half of [b]')
    conjunctions are also allowed, like in the other tactics)
 *)

Tactic Notation "symmetric" hyp(R) "using" tactic(tac) :=
  apply_by_symmetry R tac.

Tactic Notation "symmetric" "using" tactic(tac) :=
  lazymatch goal with
  | R: Chain _ |- _ => symmetric R using tac
  | _ => fail "could not find coinductive candidate of form `Chain _`"
  end.

Tactic Notation "symmetric" hyp(R) :=
  symmetric R using default_sym_tac.

Tactic Notation "symmetric" :=
  lazymatch goal with
  | R: Chain _ |- _ => symmetric R
  | _ => fail "could not find coinductive candidate of form `Chain _`"
  end.

(** * Stepping

    [step] plays one step of the coinductive game in the goal: [gfp b] becomes
    [b (gfp b)], and a chain element [`R] becomes [b `R]. [step in H] does the
    same to a hypothesis, [unstep] and [unstep in H] go the other way. Unlike
    [apply sub_bChain] these go through [leq] in the ambient lattice, so they
    work at any arity. They do not reduce [body]; follow with [simpl body] or
    [cbn [body]] if that is wanted. *)

Ltac expose_gfp_in h :=
  lazymatch type of h with
  | context [@gfp _ _ _] => idtac
  | _ =>
      tryif progress (repeat red in h) then expose_gfp_in h
      else fail 1 "[step] no greatest fixpoint in this hypothesis"
  end.

Ltac step_core :=
  match goal with
  | |- context [gfp ?b]  => apply (pfp_gfp b)
  | |- context [elem ?R] => first [apply (b_chain R) | apply (gfp_bchain R)]
  end.
Ltac step := first [ step_core | expose_gfp; step_core ].

Ltac step_in_core h :=
  match type of h with
  | context [gfp ?b] => apply (gfp_pfp b) in h
  end.
Ltac step_in h := first [ step_in_core h | expose_gfp_in h; step_in_core h ].
Tactic Notation "step" "in" ident(h) := step_in h.

Ltac unstep_core :=
  match goal with
  | |- context [gfp ?b] => apply (gfp_pfp b)
  end.
Ltac unstep := first [ unstep_core | expose_gfp; unstep_core ].

Ltac unstep_in_core h :=
  match type of h with
  | context [gfp ?b] => apply (pfp_gfp b) in h
  end.
Ltac unstep_in h := first [ unstep_in_core h | expose_gfp_in h; unstep_in_core h ].
Tactic Notation "unstep" "in" ident(h) := unstep_in h.
