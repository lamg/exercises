Require Export LogicalFoundations.Basics.
Require Export LogicalFoundations.Logic.
Require Export LogicalFoundations.Induction.
Require Export LogicalFoundations.Poly.
Require Export Init.Nat.

Fixpoint div2 (n: nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
end.

(* Collatz Step Function *)
Definition csf (n: nat): nat :=
  if even n then div2 n else (3 * n) + 1.

Fail Fixpoint reaches1_in (n: nat): nat :=
  if n =? 1 then 0
  else 1 + reaches1_in (csf n).

Fail Fixpoint Collatz_holds_for (n: nat): Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if even n then Collatz_holds_for (div2 n)
        else Collatz_holds_for (3 * n + 1)
end.

Inductive Collatz_holds_for: nat -> Prop :=
  | Chf_one: Collatz_holds_for 1
  | Chf_even (n: nat): even n = true -> Collatz_holds_for (div2 n) -> Collatz_holds_for n
  | Chf_odd (n: nat): even n = false -> Collatz_holds_for (3 * n + 1) -> Collatz_holds_for n.

Example Collatz_holds_for_12:
  Collatz_holds_for 12.
Proof.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_odd. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_even. reflexivity. simpl.
  apply Chf_one.
Qed.

Conjecture collatz:
  forall n, n <> 0 -> Collatz_holds_for n.

Inductive le: nat -> nat -> Prop :=
  | le_n (n: nat): le n n
  | le_S (n m : nat): le n m -> le n (S m).

Inductive clos_trans {t: Type} (r: t -> t -> Prop): t -> t -> Prop :=
  | t_step (x y: t): r x y -> clos_trans r x y
  | t_trans (x y z: t): clos_trans r x y -> clos_trans r y z -> clos_trans r x z.

Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of: Person -> Person -> Prop :=
  | po_SC : parent_of Sage Cleo
  | po_SR: parent_of Sage Ridley
  | po_CM: parent_of Cleo Moss.

Definition ancestor_of: Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_ex: ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with Cleo.
  - apply t_step.
    apply po_SC.
  - apply t_step.
    apply po_CM.
Qed.

Inductive clos_refl_trans {t: Type} (r: t -> t -> Prop): t -> t -> Prop :=
  | rt_step (x y: t): r x y -> clos_refl_trans r x y
  | rt_refl (x: t): clos_refl_trans r x x
  | rt_trans (x y z: t): clos_refl_trans r x y -> clos_refl_trans r y z -> clos_refl_trans r x z.

Definition cs (n m : nat): Prop := csf n = m.
Definition cms n m := clos_refl_trans cs n m.
Conjecture collatz': forall n, n <> 0 -> cms n 1.

Inductive clos_sym_refl_trans {t: Type} (r: t -> t -> Prop): t -> t -> Prop :=
  | srt_step (x y: t): r x y -> clos_sym_refl_trans r x y
  | srt_refl (x: t): clos_sym_refl_trans r x x
  | srt_sym (x y:t): clos_sym_refl_trans r x y -> clos_sym_refl_trans r y x
  | srt_trans (x y z: t): clos_sym_refl_trans r x y -> clos_sym_refl_trans r y z -> clos_sym_refl_trans r x z.

Inductive Perm3 {t: Type}: list t -> list t -> Prop :=
  | perm3_swap12 (x y z: t): Perm3 [x; y; z] [y; x; z]
  | perm3_swap23 (x y z: t): Perm3 [x; y; z] [x; z; y]
  | perm3_trans (xs ys zs: list t): Perm3 xs ys -> Perm3 ys zs -> Perm3 xs zs.

Example self_perm_123:
 Perm3 [1;2;3] [1;2;3].
(*
1 2 3
2 1 3
2 3 1
3 2 1

3 2 1
3 1 2
1 3 2
1 2 3
 *)
Proof.
  apply perm3_trans with [3;2;1].
  - apply perm3_trans with [2; 1; 3].
    + apply perm3_swap12.
    + apply perm3_trans with [2; 3; 1].
      * apply perm3_swap23.
      * apply perm3_swap12.
  - apply perm3_trans with [3; 1; 2].
    + apply perm3_swap23.
    + apply perm3_trans with [1;3;2].
      * apply perm3_swap12.
      * apply perm3_swap23.
Qed.

Inductive ev: nat -> Prop :=
  | ev_0: ev 0
  | ev_SS (n: nat) (H: ev n): ev (S (S n)).

Theorem ev_4:
  ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4':
  ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_double:
  forall n, ev (Induction.double n).
Proof.
  induction n as [|n' ind].
  - unfold double.
    simpl.
    apply ev_0.
  - unfold double.
    simpl.
    apply ev_SS.
    apply ind.
Qed.

Lemma Perm3_refl:
  forall (t: Type) (x y z: t), Perm3 [x;y;z] [x;y;z].
Proof.
  intros t x y z.
  apply perm3_trans with [z;y;x].
  - apply perm3_trans with [y;x;z].
    + apply perm3_swap12.
    + apply perm3_trans with [y; z; x].
      * apply perm3_swap23.
      * apply perm3_swap12.
  - apply perm3_trans with [z; x; y].
    + apply perm3_swap23.
    + apply perm3_trans with [x; z; y].
      * apply perm3_swap12.
      * apply perm3_swap23.
Qed.

Theorem ev_inversion:
  forall (n: nat), ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [|n' E'].
  - left. reflexivity.
  - right.
    exists n'.
    split.
    + reflexivity.
    + apply E'.
Qed.

Theorem le_inversion:
  forall (n m: nat), le n m -> (n = m) \/ (exists m', m = S m' /\ le n m').
Proof.
  intros n m E.
  destruct E as [|n' m' E'].
  - left. reflexivity.
  - right.
    exists m'.
    split.
    + reflexivity.
    + apply E'.
Qed.

Theorem evSS_ev:
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  apply ev_inversion in E.
  destruct E as [h0|h1].
  - discriminate h0.
  - destruct h1 as [n' [Hn E']].
    injection Hn as Hn.
    rewrite Hn.
    apply E'.
Qed.

Theorem evSS_ev':
  forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E' Hn].
  apply E'.
Qed.

Theorem one_not_even:
  ~ ev 1.
Proof.
  intros H.
  apply ev_inversion in H.
  destruct H as [|[m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even':
  ~ ev 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem SSSSev__even:
  forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [|n' E' Hn].
  apply evSS_ev.
  apply E'.
Qed.


Theorem ev5_nonsense:
  ev 5 -> (plus 2 2 = 9).
Proof.
  intros H.
  inversion H as [|n' E' Hn].
  apply evSS_ev in E'.
  inversion E' as [|n'' E'' Hnn].
Qed.

Theorem inversion_ex1:
  forall (n m p: nat), [n;m] = [p;p] -> [n] = [m].
Proof.
  intros n m p H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2:
  forall (n:nat), S n = O -> plus 2 2 = 5.
Proof.
  intros n H.
  inversion H.
Qed.

Lemma ev_Even_firsttry:
  forall n, ev n -> Even n.
Proof.
  intros n H.
  unfold Even.
  inversion H as [E | n' H' E].
  - exists 0. reflexivity.
  - assert (h0: (exists k, n' = Induction.double k) -> (exists n0, S (S n') = Induction.double n0)).
    + intros [k E'].
      exists (S k).
      simpl.
      simpl.
      rewrite E'.
      reflexivity.
    + apply h0.
      generalize dependent E.
      Abort.

Lemma ev_Even:
  forall n, ev n -> Even n.
Proof.
  unfold Even.
  intros n E.
  induction E as [|n' E' ind].
  - exists 0. reflexivity.
  - destruct ind as [n H].
    exists (S n).
    simpl.
    rewrite H.
    reflexivity.
Qed.

Theorem ev_Even_iff:
  forall n, ev n <-> Even n.
Proof.
  intros n.
  split.
  - apply ev_Even.
  - unfold Even.
    intros [k E].
    rewrite E.
    apply ev_double.
Qed.

Theorem ev_sum:
  forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H0 H1.
  induction H0 as [|n' E ind].
  - apply H1.
  - simpl.
    apply ev_SS.
    apply ind.
Qed.

Theorem ev_ev__ev:
  forall n m, ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H0 H1.
  induction H1 as [|n' E ind].
  - apply H0.
  - inversion H0 as [|n'' E' H].
    apply ind.
    apply E'.
Qed.

Theorem ev_plus_plus:
  forall n m p, ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p H0 H1.
  assert (H: ev (n+m + (n+p))).
  - apply ev_sum.
    apply H0.
    apply H1.
  - rewrite <- add_assoc in H.
    rewrite (add_commutativity n p) in H.
    rewrite (add_assoc m p n) in H.
    rewrite (add_commutativity (m + p) n) in H.
    rewrite add_assoc in H.
    apply (ev_ev__ev (n + n) (m + p)) in H.
    + apply H.
    + rewrite <- double_plus.
      apply ev_double.
Qed.

Inductive ev': nat -> Prop :=
  | ev'_0: ev' 0
  | ev'_2: ev' 2
  | ev'_sum n m (Hn: ev' n) (Hm: ev' m): ev' (n + m).

Theorem ev'_ev:
  forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intro H.
    induction H as [ | | n' m H0 H1 H2 ind].
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply H1.
      * apply ind.
  - intro H.
    induction H as [|n' E ind].
    + apply ev'_0.
    + apply (ev'_sum 2 n' ev'_2 ind).
Qed.

Lemma Perm3_symm:
  forall (t: Type) (xs ys: list t),
    Perm3 xs ys -> Perm3 ys xs.
Proof.
  intros t xs ys E.
  induction E as [x y z | x y z | xs ys zs E__xy H__xy E__yz H__yz].
  - apply perm3_swap12.
  - apply perm3_swap23.
  - apply (perm3_trans _ ys _).
    + apply H__yz.
    + apply H__xy.
Qed.

Lemma or_symmetry:
  forall x y, x \/ y <-> y \/ x.
Proof.
  intros x y.
  split.
  - intros H. apply or_commutativity. apply H.
  - intros H. apply or_commutativity. apply H.
Qed.

Print "\/".

Lemma Perm3_In:
  forall (t: Type) (x: t) (xs ys: list t),
    Perm3 xs ys -> In x xs -> In x ys.
Proof.
  intros t x xs ys Hperm Hin.
  induction Hperm as [ | | xs ys zs Perm__xs  Ind__xs Perm__ys Ind__ys ].
  - simpl. simpl in Hin.
    rewrite or_assoc.
    rewrite (or_symmetry (x = y) (x = x0)).
    rewrite <- or_assoc.
    apply Hin.
  - simpl. simpl in Hin.
    rewrite or_assoc.
    rewrite (or_assoc (x = x0 \/ x = z)).
    rewrite <- (or_assoc (x = x0) (x = z) (x = y)).
    rewrite (or_symmetry (x = z) (x = y)).
    rewrite or_assoc.
    rewrite <- (or_assoc (x = x0 \/ x = y) (x = z) False).
    rewrite <- or_assoc.
    apply Hin.
  - apply Ind__ys.
    apply Ind__xs.
    apply Hin.
Qed.

Lemma Perm3_NotIn:
  forall (t : Type) (x: t) (xs ys : list t),
    Perm3 xs ys -> ~In x xs -> ~In x ys.
Proof.
  intros t x xs ys Hperm Hin_xs Hin_ys.
  apply Hin_xs.
  apply (Perm3_In t x ys xs).
  - apply Perm3_symm.
    apply Hperm.
  - apply Hin_ys.
Qed.

Example Perm3_example2:
  ~ Perm3 [1;2;3] [1;2;4].
Proof.
  intro H.
  apply (Perm3_NotIn t 4 [1;2;3] [1;2;4]).
  - apply H.
  - unfold not.
    simpl.
    intro in4.
    destruct in4.
    + discriminate H0.
    + destruct H0.
      * discriminate H0.
      * destruct H0.
        -- discriminate H0.
        -- apply H0.
  - simpl.
    right.
    right.
    left.
    reflexivity.
Qed.

Notation "n <= m" := (le n m).

Theorem test_le1:
  3 <= 3.
Proof.
  apply le_n.
Qed.

Theorem test_le2:
  3 <= 6.
Proof.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Theorem test_le3:
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H.
  inversion H.
  inversion H2.
Qed.

Definition ge (m n : nat) : Prop := le n m.
Notation "m >= n" := (ge m n).

Lemma le_monotonicity:
  forall n m, n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [|n' E ind].
  - apply le_n.
  - apply le_S.
    apply IHind.
Qed.

Lemma le_trans:
  forall m n p, m <= n -> n <= p -> m <= p.
Proof.
  intros m n p H0 H1.
  induction H1.
  - apply H0.
  - apply IHle in H0.
    apply le_S in H0.
    apply H0.
Qed.

Theorem O_le_n:
  forall n, 0 <= n.
Proof.
  intros n.
  induction n.
  - apply le_n.
  - apply le_S in IHn.
    apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm:
  forall n m, n <= m -> S n <= S m.
Proof.
  apply le_monotonicity.
Qed.

Theorem le_plus_l:
  forall x y, x <= x + y.
Proof.
  intros x y.
  induction x.
  - simpl. apply O_le_n.
  - apply (le_monotonicity x (x + y)).
    apply IHx.
Qed.

Theorem plus_le:
  forall x y z,
    x + y <= z  ->  x <= z /\ y <= z.
Proof.
  intros x y z H.
  split.
  - apply (le_trans x (x + y) z).
    + apply le_plus_l.
    + apply H.
  - apply (le_trans y (x + y) z).
    + rewrite add_commutativity.
      apply le_plus_l.
    + apply H.
Qed.

Lemma plus_1_is_S:
  forall n m, S n + m = n + m + 1.
Proof.
  intros n m.
  simpl.
  rewrite <- (plus_n_S_m (n + m) 0).
  rewrite add_0_right.
  reflexivity.
Qed.

Lemma S_is_plus_1:
  forall n, S n = n + 1.
Proof.
  intro n.
  rewrite <- (plus_n_S_m n 0).
  rewrite add_0_right.
  reflexivity.
Qed.

Theorem plus_le_cases:
  forall n m p q,
    n + m <= p + q  ->  n <= p \/ m <= q.
Proof.
  intros n m p q H.
  induction n.
  - left.
    apply O_le_n.
  - left.
    rewrite S_is_plus_1.
