From Rocq Require Export Basics.
Require Import Coq.Init.Nat.
Import NatPlayground.

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
    - rewrite ind.
      rewrite negb_is_involutive.
      simpl.
      reflexivity.
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

Theorem mult_commutativity :
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

Theorem zero_neqb_S:
  forall n:nat,
  0 =? S n = false.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r:
  forall b,
  andb b false = false.
Proof.
  intro b.
  destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0:
  forall n:nat,
  S n =? 0 = false.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l:
  forall n,
  1 * n = n.
Proof.
  intro n.
  simpl.
  rewrite add_0_right.
  reflexivity.
Qed.

Theorem all3_spec:
  forall a b:bool,
  orb (andb a b) (orb (negb a) (negb b)) = true.
Proof.
  intros a b.
  destruct a eqn:E.
  - simpl. destruct b eqn:F.
    + reflexivity.
    + reflexivity.
  - simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r:
  forall n m p,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [|p' ind ].

  - rewrite mul_0_right. rewrite mul_0_right. rewrite mul_0_right. reflexivity.
  - rewrite <- mult_n_S_m.
    rewrite <- mult_n_S_m.
    rewrite <- mult_n_S_m.
    rewrite ind.
    rewrite <- add_assoc.
    rewrite <- add_assoc.
    assert (H: m*p' + (n + m) = (n + (m*p' + m))).
    + rewrite add_shuffle3. reflexivity.
    + rewrite H. reflexivity.
Qed.

Theorem mult_assoc:
  forall n m p,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' ind].
  - rewrite mult_0_n. rewrite mult_0_n. reflexivity.
  - simpl. rewrite mult_plus_distr_r. rewrite ind. reflexivity.
Qed.

Theorem add_shuffle3':
  forall n m p,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc.
  replace (n + m) with (m + n).
  - rewrite add_assoc.
    reflexivity.
  - rewrite add_commutativity. reflexivity.
Qed.

Ltac refl := reflexivity.

Import BinaryNumerals.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

  Fixpoint incr (m: bin) :=
    match m with
    | B0 b => B1 b
    | B1 b => B0 (incr b)
    | Z => B1 Z
  end.


  Fixpoint bin_to_nat (m:bin):nat :=
    match m with
    | Z => O
    | B0 b => double (bin_to_nat b)
    | B1 b => S (double (bin_to_nat b))
  end.

Theorem bin_to_nat_pres_incr:
  forall b,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intro b.
  induction b as [|b0 ind0 |b1 ind1].
  - simpl. refl.
  - simpl. refl.
  - simpl.
    rewrite ind1.
    simpl.
    refl.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_bin_nat:
  forall n,
  bin_to_nat(nat_to_bin n) = n.
Proof.
  intro n.
  induction n as [|n' ind].
  - simpl. refl.
  - simpl.
    rewrite bin_to_nat_pres_incr.
    rewrite ind.
    refl.
Qed.

Theorem bin_nat_bin_fails:
  forall b,
  nat_to_bin (bin_to_nat b) = b.
Proof.
  intro b.
  destruct b eqn:E.
  - simpl. refl. (* goal unsatisfiable: B0 Z = Z*)
  - simpl.
Abort.

Lemma double_incr:
  forall n,
  double (S n) = S (S (double n)).
Proof.
  intro n.
  simpl.
  refl.
Qed.

Definition double_bin(b:bin) :=
  match b with
  | Z => Z
  | _ => B0 b
  end.

Example double_bin_zero:
  double_bin Z = Z.
Proof. refl. Qed.

Lemma double_incr_bin:
  forall b,
  double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intro b.
  destruct b eqn:E.
  - simpl. refl.
  - simpl. refl.
  - simpl. refl.
  Qed.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | B0 b' => double_bin (normalize b')
  | B1 b' => incr (double_bin (normalize b'))
end.

Example normalize_Z:
  normalize Z = Z.
Proof. refl. Qed.

Example normalize_B1_Z:
  normalize (B1 Z) = B1 Z.
Proof. refl. Qed.

Example normalize_B0_Z:
  normalize (B0 Z) = Z.
Proof. refl. Qed.

Example normalize_100:
  normalize (B0 (B0 (B1 (B0 Z)))) = (B0 (B0 (B1 Z))).
Proof. refl. Qed.

Lemma double_nat_bin:
  forall n,
  nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  intro n.
  induction n as [|n' ind].
  - simpl. refl.
  - rewrite double_incr.
    simpl.
    rewrite double_incr_bin.
    rewrite ind.
    refl.
Qed.

Theorem bin_nat_bin:
  forall b,
  nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intro b.
  induction b as [|b0 ind0|b1 ind1].
  - simpl. refl.
  - simpl.
    rewrite double_nat_bin.
    rewrite ind0.
    refl.
  - simpl.
    rewrite double_nat_bin.
    rewrite ind1.
    refl.
Qed.
