From LF Require Export Basics.

Import NatPlayground.

Theorem add_zero_right : 
  forall n:nat,
  n + zero = n.
  Proof.
    intros n.
    induction n as [|n' ind].
    - reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

Theorem minus_n_n :
  forall n, minus n n = zero.
  Proof.
  intros n. induction n as [| n' ind].
  - simpl. reflexivity.
  - simpl. rewrite ind. reflexivity. 
  Qed.

Theorem mul_zero_right: 
  forall n:nat,
  n * zero = zero.
  Proof.
    intros n.
    induction n as [|n' ind].
    - reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

Theorem plus_n_succ_m : 
  forall n m : nat,
  succ (n + m) = n + (succ m).
  Proof.
    intros n m.
    induction n as [|n' ind].
    - reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

Theorem add_commutativity : 
  forall n m : nat,
  n + m = m + n.
  Proof.
    intros n m.
    induction n as [|n' ind].
    - rewrite add_zero_right. reflexivity.
    - simpl. rewrite ind. rewrite plus_n_succ_m. reflexivity.
  Qed.


Theorem add_assoc : 
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
  Proof.
    intros n m p.
    induction n as [|n' ind].
    - simpl. reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

