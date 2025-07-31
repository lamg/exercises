From Rocq Require Export Basics.

Import NatPlayground.
Require Import Coq.Init.Nat.

Theorem add_0_right : 
  forall n:nat,
  n + 0 = n.
  Proof.
    intros n.
    induction n as [|n' ind].
    - reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

Theorem minus_n_n :
  forall n, minus n n = 0.
  Proof.
  intros n. induction n as [| n' ind].
  - simpl. reflexivity.
  - simpl. rewrite ind. reflexivity. 
  Qed.

Theorem mul_0_right: 
  forall n:nat,
  n * 0 = 0.
  Proof.
    intros n.
    induction n as [|n' ind].
    - reflexivity.
    - simpl. rewrite ind. reflexivity.
  Qed.

Theorem plus_n_S_m : 
  forall n m : nat,
  S (n + m) = n + (S m).
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
    - rewrite add_0_right. reflexivity.
    - simpl. rewrite ind. rewrite plus_n_S_m. reflexivity.
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
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus:
  forall n,
  double n  = n + n.
  Proof.
    intros n.
    induction n as [|n' ind].
    - simpl. reflexivity.
    - simpl. rewrite ind. rewrite plus_n_S_m. reflexivity. 
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
  even (S n) = negb (even n).
  Proof.
    intros n.
    induction n as [|n' ind].
    - simpl. reflexivity.
    - rewrite ind. rewrite negb_is_involutive. simpl. reflexivity.
  Qed.

Theorem mult_0_plus' : 
  forall n m : nat,
  (n + 0 + 0) * m = n * m.
  Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
      rewrite add_commutativity. 
      simpl. 
      rewrite add_commutativity. 
      reflexivity.
    rewrite H.
    reflexivity.
  Qed.

Theorem plus_rearrange_firsttry: 
  forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (h: n + m = m + n).
    rewrite add_commutativity.
    reflexivity.
  rewrite h.
  reflexivity.
Qed.

Theorem add_shuffle3:
  forall n m p :nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (h: n + m = m + n).
    rewrite add_commutativity.
    reflexivity.
  rewrite add_assoc.
  rewrite h.
  rewrite add_assoc.
  reflexivity.
Qed.

Theorem mult_n_S_m:
    forall n m: nat,
    n * m + n = n * S m.
Proof. 
  intros n m.
  induction n as [|n' ind].
  - rewrite mult_0_n. reflexivity.
  - rewrite <- plus_n_S_m. 
    simpl. 
    rewrite <- ind.
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mul_commutativity : 
  forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [|n' ind].
  - rewrite mul_0_right. 
    reflexivity.
  - simpl. 
    rewrite <- mult_n_S_m. 
    rewrite ind.
    rewrite add_commutativity.
    reflexivity.
Qed.

(* monotonicity of + and ≤ *)
Theorem plus_leb_compat_l:
  forall n m p: nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  induction p as [|p' ind].
  - intro a. assumption.
  - intro a.
    simpl.
    rewrite ind.
    + reflexivity.
    + assumption. 
Qed.

Theorem leb_refl:
  forall n:nat,
  n <=? n = true.
Proof.
  intro n.
  induction n as [|n' ind].
  - reflexivity.
  - simpl. assumption.
Qed.
   
