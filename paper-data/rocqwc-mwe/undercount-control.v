Definition f (A : Type) (x : A) := x.

Instance foo (y : nat) : f nat 0 = 0.
Proof.
  reflexivity.
Qed.
