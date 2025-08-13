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

Theorem double_injective_take2_FAILED:
  forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  induction m as [|m' ind].
  - simpl.
    intros eq.
    destruct n as [|n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq.
    destruct n as [|n'] eqn:E.
    + discriminate eq.
    + f_equal.
Abort.

Theorem double_injective_take2:
  forall n m, double n = double m -> m = n.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' ind].
  - simpl.
    intros n eq.
    destruct n as [|n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl.
    intros n eq.
    destruct n as [|n'] eqn:E.
    + discriminate eq.
    + f_equal.
      apply ind.
      injection eq as goal.
      apply goal.
Qed.

Import OptionPlayground.

Theorem nth_error_after_last:
  forall (n: nat) (t : Type) (xs: list t),
    length xs = n -> nth_error xs n = None.
Proof.
  intros n t xs eq.
  generalize dependent xs.
  induction n as [|n' ind].
  - intros xs eq.
    destruct xs eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros xs eq.
    destruct xs eqn:E.
    + reflexivity.
    + simpl.
      injection eq as goal.
      apply ind.
      apply goal.
Qed.

Definition square n := n * n.

Import Induction.

Lemma square_mult:
  forall n m,
    square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
    + rewrite mult_commutativity.
      rewrite mult_assoc.
      reflexivity.
    + rewrite H.
      rewrite mult_assoc.
      reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1:
  forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | 0 => 5
  | S _ => 5
  end.

Fact silly_fact_2_failed:
  forall m, bar m + 1  = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.


Fact silly_fact_2:
  forall m, bar m + 1  = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Fact silly_fact_2':
  forall m, bar m + 1  = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n: nat): bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false:
  forall (n: nat), sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (n =? 3) eqn:E.
  - reflexivity.
  - destruct (n =? 5) eqn:F.
    + reflexivity.
    + reflexivity.
Qed.

Theorem prod_eq_fst:
  forall (t u : Type) (w x:t) (y z:u),
    (w, y) = (x, z) -> w = x.
Proof.
  intros t u w x y z eq.
  injection eq.
  intros a b.
  apply b.
Qed.

Definition combine_uncurried {t u: Type} := @prod_uncurry (list t) (list u) (list (t * u)) combine.

Theorem combine_split_uncurried:
  forall t u (xs: list (t * u)),
    combine_uncurried (split xs) = xs.
Proof.
  intros t u xs.
  induction xs as [|x xs' ind].
  - reflexivity.
  - destruct x.
    simpl.
    destruct (split xs').
    rewrite <- ind.
    unfold combine_uncurried.
    unfold prod_uncurry.
    unfold fst.
    unfold snd.
    reflexivity.
Qed.

Theorem combine_split:
  forall t u (xs: list (t * u)) ys zs,
    split xs = (ys, zs) -> combine ys zs = xs.
Proof.
   intros t u xs ys zs eq.
   rewrite <- combine_split_uncurried.
   unfold combine_uncurried.
   unfold prod_uncurry.
   rewrite eq.
   unfold fst.
   unfold snd.
   reflexivity.
Qed.

Definition sillyfun1 (n: nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED:
  forall (n:nat), sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (n =? 3).
Abort.

Theorem sillyfun1_odd:
  forall (n:nat), sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:E.
  - apply eqb_true in E.
    rewrite E.
    reflexivity.
  - destruct (n =? 5) eqn:F.
    + apply eqb_true in F.
      rewrite F.
      reflexivity.
    + discriminate eq.
Qed.

Theorem bool_fn_applied_thrice:
  forall (f: bool -> bool) (b: bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:E.
  - destruct (f true) eqn:F.
    + rewrite F. apply F.
    + destruct (f false) eqn:G.
      * apply F.
      * apply G.
  - destruct (f false) eqn:F.
    + destruct (f true) eqn:G.
      * apply G.
      * apply F.
    + rewrite F. apply F.
Qed.

Import Induction.

Theorem eqb_sym:
  forall (n m : nat), (n =? m) = (m =? n).
Proof.
  intros n m.
  generalize dependent m.
  induction n as [|n' ind].
  - destruct m eqn:F.
    + reflexivity.
    + rewrite zero_neqb_S.
      rewrite S_neqb_0.
      reflexivity.
  - destruct m eqn:F.
    + rewrite zero_neqb_S.
      rewrite S_neqb_0.
      reflexivity.
    + simpl.
      apply ind.
Qed.
