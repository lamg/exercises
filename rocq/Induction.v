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

Fixpoint double (n:nat) :=
  match n with
  | zero => zero
  | succ n' => succ (succ (double n'))
  end.

Lemma double_plus:
  forall n,
  double n  = n + n.
  Proof.
    intros n.
    induction n as [|n' ind].
    - simpl. reflexivity.
    - simpl. rewrite ind. rewrite plus_n_succ_m. reflexivity. 
  Qed.

Theorem eqb_refl: 
  forall n : nat,
  (n =? n) = true.
  Proof.
    intros n.
    induction n as [|n' ind].
    - simpl. reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

Theorem even_succ : 
  forall n : nat,
  even (succ n) = negb (even n).
  Proof.
    intros n.
    induction n as [|n' ind].
    - simpl. reflexivity.
    - rewrite ind. rewrite negb_is_involutive. simpl. reflexivity.
  Qed.

Theorem mult_zero_plus' : 
  forall n m : nat,
  (n + zero + zero) * m = n * m.
  Proof.
    intros n m.
    assert (H: n + zero + zero = n).
      rewrite add_commutativity. simpl. rewrite add_commutativity. 
      reflexivity.
    rewrite H.
    reflexivity. 
  Qed.
