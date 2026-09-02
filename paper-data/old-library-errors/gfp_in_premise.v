(* The released rocq-coinduction rejects a goal whose premise mentions the
   same greatest fixed point as its conclusion. The shape is routine: in
   InteractionTrees it is every lemma that assumes one bisimilarity to conclude
   another, such as eqit_Proper_R in theories/Eq/Eqit.v.

   Against the released library this fails.  Against the rewritten one it is
   accepted.  Compile with the loadpath in this directory's README. *)

From Coinduction Require Import all.
Import CoindNotations.

Section Premise.
  Variable b : mon (nat -> nat -> Prop).

  Goal forall x y, gfp b x y -> gfp b x y.
    coinduction R CIH.
  Abort.
End Premise.
