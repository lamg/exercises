From Rocq Require Export Poly.
From Rocq Require Export Basics.
Import NatPlayground.
From Rocq Require Export Induction.

Theorem silly0:
  forall (n m : nat), n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly1:
  forall (m n p q: nat),
    n = m -> (n = m -> [n; p] = [m; q]) -> [n;p] = [m;q].
Proof.
  intros m n p q eq0 eq1.
  apply eq1.
  apply eq0.
Qed.

Theorem silly1':
  forall (n m : nat),
    (n,n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq0 eq1.
  apply eq1.
  apply eq0.
Qed.

Theorem silly_ex:
  forall p,
    (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
    even p = true ->
    odd (S p) = true.
Proof.
  intros p s_even not_even even_p.
  apply not_even.
  apply s_even.
  apply even_p.
Qed.

Theorem silly3:
  forall (n m : nat), n = m -> m = n.
Proof.
  intros n m eq.
  symmetry.
  apply eq.
Qed.

Theorem rev_exercise1:
  forall (xs ys : list nat),
    xs = rev ys -> ys = rev xs.
Proof.
  intros xs ys eq.
  apply rev_injective.
  rewrite rev_involutive.
  symmetry.
  apply eq.
Qed.

Example trans_eq_example:
  forall (a b c d e f: nat),
    [a; b] = [c; d] -> [c;d] = [e;f] -> [a; b] = [e;f].
Proof.
  intros a b c d e f eq0 eq1.
  rewrite eq0.
  rewrite eq1.
  reflexivity.
Qed.

Theorem trans_eq:
  forall (t: Type) (m n p: t),
    n = m -> m = p -> n = p.
Proof.
  intros t m n p eq0 eq1.
  rewrite eq0.
  rewrite eq1.
  reflexivity.
Qed.


Example trans_eq_example':
  forall (a b c d e f: nat),
    [a; b] = [c; d] -> [c;d] = [e;f] -> [a; b] = [e;f].
Proof.
  intros a b c d e f eq0 eq1.
  apply trans_eq with (m := [c;d]).
  - apply eq0.
  - apply eq1.
Qed.

Example trans_eq_example'':
  forall (a b c d e f: nat),
    [a; b] = [c; d] -> [c;d] = [e;f] -> [a; b] = [e;f].
Proof.
  intros a b c d e f eq0 eq1.
  transitivity [c;d].
  - apply eq0.
  - apply eq1.
Qed.


Example trans_eq_exercise :
  forall (n m p q : nat),
     m = (minus2 p) -> (n + q) = m -> (n + q) = (minus2 p).
Proof.
  intros n m p q eq0 eq1.
  transitivity m.
  - apply eq1.
  - apply eq0.
Qed.

Theorem S_injective:
  forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m eq0.
  assert (eq1: n = pred (S n)). reflexivity.
  rewrite eq1.
  rewrite eq0.
  simpl.
  reflexivity.
Qed.

Theorem S_injective':
  forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m eq.
  injection eq as inj.
  apply inj.
Qed.

Theorem injection_ex1:
  forall (n m p: nat), [n; m] = [p; p] -> n = m.
Proof.
  intros n m p eq.
  injection eq as inj0 inj1.
  rewrite inj0.
  rewrite inj1.
  reflexivity.
Qed.

Theorem injection_ex3:
  forall (t: Type) (x y z: t) (xs ys: list t),
    x :: y :: xs = z :: ys  ->  ys = z :: xs  ->  x = y.
Proof.
  intros t x y z xs ys.
  intros eq0 eq1.
  injection eq0 as inj0 inj1.
  assert (eq_yz: y :: xs = z :: xs).
  - transitivity ys.
    apply inj1.
    apply eq1.
  - injection eq_yz as inj2.
    transitivity z.
    + rewrite inj0. reflexivity.
    + rewrite inj2. reflexivity.
Qed.

Theorem discriminate_ex1:
  forall (m n: nat), false = true -> m = n.
Proof.
  intros m n contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2:
  forall (n : nat), S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Example discriminate_ex3 :
  forall (t : Type) (x y z : t) (xs ys : list t),
    x :: y :: xs = [] -> x = z.
Proof.
  intros t x y z xs ys contra.
  discriminate contra.
Qed.

Example eqb_0_l:
  forall n, 0 =? n = true -> n = 0.
Proof.
  intros n eq.
  destruct n as [|n'] eqn:E.
  - reflexivity.
  - discriminate.
Qed.

Theorem leibniz:
  forall (t u : Type) (f: t -> u) (x y : t),
    x = y -> f x = f y.
Proof.
  intros t u f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal':
  forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m eq.
  f_equal.
  apply eq.
Qed.

Theorem S_inj:
  forall (n m : nat) (b: bool),
    (S n =? S m) = b  ->  (n =? m) = b.
Proof.
  intros n m b eq.
  simpl in eq.
  apply eq.
Qed.

Theorem silly4:
  forall (n m p q: nat), (n = m -> p = q)  ->  m = n  ->  q = p.
Proof.
  intros n m p q eq0 eq1.
  symmetry in eq0.
  apply eq0.
  symmetry in eq1.
  apply eq1.
Qed.

Theorem specialize_example:
  forall n, (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_commutativity in H.
  simpl in H.
  apply H.
Qed.

Example trans_eq_example''':
  forall (a b c d e f: nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq0 eq1.
  specialize trans_eq with (m := [c;d]) as H.
  apply H.
  apply eq0.
  apply eq1.
Qed.

Theorem double_injective:
  forall (n m : nat), double n = double m -> n = m.
Proof.
  intros n.
  induction n as [|n' ind].
  - intros m eq.
    destruct m eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m eqn:E.
    + discriminate eq.
    + f_equal.
      apply ind.
      simpl in eq.
      injection eq as goal.
      apply goal.
Qed.

Theorem eqb_true:
  forall (n m : nat),
    n =? m = true -> n = m.
Proof.
  intro n.
  induction n as [|n' ind].
  - intros m eq.
    destruct m eqn:E.
    + simpl. reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m eqn:E.
    + discriminate eq.
    + f_equal.
      apply ind.
      simpl in eq.
      apply eq.
Qed.

Theorem plus_n_n_injective:
  forall (n m : nat),
    n + n = m + m -> n = m.
Proof.
  intro n.
  induction n as [|n' ind].
  - intros m eq.
    destruct m eqn:E.
    + reflexivity.
    + discriminate eq.
  - intro m.
    destruct m eqn:E.
    + intro eq. discriminate eq.
    + simpl.
      rewrite <- plus_n_S_m.
      rewrite <- plus_n_S_m.
      intro eq.
      f_equal.
      apply ind.
      injection eq as goal.
      apply goal.
Qed.
