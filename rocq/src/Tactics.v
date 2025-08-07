From Rocq Require Export Poly.

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
  Print rev_injective.
  apply rev_injective.
