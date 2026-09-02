Definition f (A : Type) (x : A) := x.

Instance foo (y : nat) (z := f nat y) : f nat 0 = 0.
Proof.
  reflexivity.
Qed.
