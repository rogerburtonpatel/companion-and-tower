(** * Facts about [eqit], pared down from InteractionTrees [Eq/Eqit.v]

    Everything is specialised to [eqit RR true true], which is [eutt].  That
    removes the [CHECK] side conditions carried by the tau-stripping rules.

    NOTE ON AXIOMS.  [dependent destruction] below uses [Eqdep.Eq_rect_eq]
    (UIP).  The rest of this development is closed under the global context.
    InteractionTrees avoids the axiom by eliminating [eqitF] with a hand-written
    [match] whose return clause is [True] off the [VisF] branch, see
    [eqitF_inv_VisF_r] in [Eq/Eqit.v]. *)

From Stdlib Require Import Program.Equality.
Require Import lattice tower.
Require Import diacritical_tower_example.

Section inv.
  Context {E : Type -> Type} {R : Type} (RR : R -> R -> Prop).
  Notation T := (itree E R).
  Notation Relr := (T -> T -> Prop).

  (** A derivation ending at a [Vis] on the right either matches that [Vis]
      directly, or strips a tau on the left. *)
  Lemma eqitF_inv_VisF_r {sim : Relr} ot1 X (e : E X) (k2 : X -> T) :
    eqitF RR true true sim ot1 (VisF e k2) ->
    (exists k1, ot1 = VisF e k1 /\ forall v, sim (k1 v) (k2 v)) \/
    (exists t1', ot1 = TauF t1' /\ eqitF RR true true sim (observe t1') (VisF e k2)).
  Proof.
    intro H. dependent destruction H; eauto.
  Qed.

  (** The mirror image, for a [Vis] on the left. *)
  Lemma eqitF_inv_VisF_l {sim : Relr} ot2 X (e : E X) (k1 : X -> T) :
    eqitF RR true true sim (VisF e k1) ot2 ->
    (exists k2, ot2 = VisF e k2 /\ forall v, sim (k1 v) (k2 v)) \/
    (exists t2', ot2 = TauF t2' /\ eqitF RR true true sim (VisF e k1) (observe t2')).
  Proof.
    intro H. dependent destruction H; eauto.
  Qed.

End inv.
