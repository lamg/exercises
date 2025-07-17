
From LF Require Export Basics.

Import NatPlayground.

Theorem add_0_r_firsttry : 
  forall n:nat,
  n + zero = n.
  Proof.
    intros n.
    induction n as [|n ind].
    - reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

