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

Definition lt (n m: nat) := le (S n) m.
Notation "n < m" := (lt n m).

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

Lemma s_n_le_n:
  forall n m, S n <= m -> n <= m.
Proof.
  intros n m H.
  induction n.
  - apply O_le_n.
  - inversion H.
    + apply le_S. apply le_n.
    + rewrite H2.
      apply (le_trans _ (S (S n)) _).
      * apply le_S. apply le_n.
      * apply H.
Qed.

Lemma cases_le_plus:
  forall n m p, n <= m \/ n <= p -> n <= m + p.
Proof.
  intros n m p H.
  destruct H.
  - apply (le_trans _ m _).
    + apply H.
    + apply le_plus_l.
  - apply (le_trans _ p _).
    + apply H.
    + rewrite add_commutativity.
      apply le_plus_l.
Qed.

Lemma s_n_pred_m:
  forall n m, S n <= m -> n <= pred m.
Proof.
  intros n m H.
  induction n.
  - apply O_le_n.
  - inversion H.
    + simpl. apply le_n.
    + simpl.
      apply s_n_le_n in H0.
      apply H0.
Qed.

Theorem le_monotonicity_rev:
  forall n m, S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  - apply le_n.
  - apply s_n_le_n.
    apply H2.
Qed.
 
Theorem plus_le_cases:
  forall n m p q,
    n + m <= p + q  ->  n <= p \/ m <= q.
Proof.
  intros n m p q H.
  generalize dependent m.
  generalize dependent p.
  generalize dependent q.
  induction n.
  - intros q p m H.
    simpl in H.
    destruct p.
    + left. apply le_n.
    + left. apply O_le_n.
  - intros q p m H.
    destruct p.
    + right.
      inversion H.
      * apply plus_le in H.
        simpl in H.
        destruct H.
        apply H2.
      * apply plus_le in H.
        simpl in H.
        destruct H.
        apply H3.
    + simpl in H.
      rewrite plus_n_S_m in H.
      rewrite plus_n_S_m in H.
      apply IHn in H.
      destruct H.
      * left.
        apply le_monotonicity.
        apply H.
      * right.
        apply le_monotonicity_rev.
        apply H.
Qed.

Theorem plus_le_compat_l:
  forall n m p, n <= m -> p + n <= p + m.
Proof.
  intros n m p H.
  induction p.
  - simpl. apply H.
  - simpl.
    apply le_monotonicity.
    apply IHp.
Qed.

Theorem plus_le_compat_r:
  forall n m p, n <= m -> n + p <= m + p.
Proof.
  intros n m p H.
  induction p.
  - rewrite add_0_right.
    rewrite add_0_right.
    apply H.
  - rewrite <- plus_n_S_m.
    rewrite <- plus_n_S_m.
    apply le_monotonicity.
    apply IHp.
Qed.

Theorem le_plus_trans:
  forall n m p, n <= m -> n <= m + p.
Proof.
  intros n m p H.
  induction p.
  - rewrite add_0_right. apply H.
  - apply le_S in IHp.
    simpl in IHp.
    rewrite plus_n_S_m in IHp.
    apply IHp.
Qed.


Theorem lt_ge_cases:
  forall n m, n < m \/ n >= m.
Proof.
  intros n m.
  induction n.
  - destruct m.
    + right. apply le_n.
    + left.
      unfold lt.
      apply le_monotonicity.
      apply O_le_n.
  - destruct m.
    + right.
      unfold ge.
      apply O_le_n.
    + destruct IHn.
      unfold lt in H.
      unfold lt.
      inversion H.
      * right. unfold ge. apply le_n.
      * left.
        apply le_monotonicity.
        apply H2.
      * right.
        unfold ge.
        unfold ge in H.
        apply le_S in H.
        apply H.
Qed.

Theorem n_lt_m__n_le_m:
  forall n m, n < m -> n <= m.
Proof.
  intros n m H.
  unfold lt in H.
  apply s_n_le_n in H.
  apply H.
Qed.

Lemma O_lt_s_n:
  forall n, 0 < S n.
Proof.
  intros n.
  destruct n.
  - unfold lt. apply le_n.
  - unfold lt. apply le_monotonicity. apply O_le_n.
Qed.

Lemma n_lt_s_n:
  forall n, n < S n.
Proof.
  intros n.
  unfold lt.
  apply le_n.
Qed.

Theorem plus_lt:
  forall n m p, n + m < p -> n < p /\ m < p.
Proof.
  intros n m p H.
  generalize dependent m.
  generalize dependent p.
  induction n.
  - intros p m H'.
    inversion H'.
    + simpl.
      split.
      * apply O_lt_s_n.
      * apply n_lt_s_n.
    + split.
      * apply O_lt_s_n.
      * simpl in H'.
        rewrite H1.
        apply H'.
  - intros p m H.
    inversion H.
    + simpl.
      split.
      * apply le_monotonicity. apply le_monotonicity. apply le_plus_l.
      * unfold lt.
        apply le_monotonicity.
        rewrite add_commutativity.
        rewrite plus_n_S_m.
        apply le_plus_l.
    + rewrite plus_n_S_m in H0.
      apply plus_le in H0.
      destruct H0.
      unfold lt.
      split.
      * apply le_monotonicity.
        apply H0.
      * apply le_monotonicity.
        apply s_n_le_n.
        apply H3.
Qed.

Theorem leb_complete:
  forall n m, n <=? m = true -> n <= m.
Proof.
  intros n m H.
  induction n.
  - apply O_le_n.
  - apply leb_plus_exists in H.
    destruct H.
    rewrite H.
    apply le_plus_l.
Qed.

Theorem leb_correct:
  forall n m, n <= m -> n <=? m = true.
Proof.
  intros n m H.
  generalize dependent m.
  induction n.
  - simpl. reflexivity.
  - intros m H.
    inversion H.
    + apply leb_refl.
    + apply IHn.
      apply s_n_le_n in H0.
      apply H0.
Qed.

Theorem leb_iff:
  forall n m, n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans:
  forall n m p, n <=? m = true -> m <=? p = true -> n <=? p = true.
Proof.
  intros n m p.
  rewrite leb_iff.
  rewrite leb_iff.
  rewrite leb_iff.
  apply le_trans.
Qed.

Inductive R: nat -> nat -> nat -> Prop :=
  | c0 : R 0 0 0
  | c1 m n p (H: R m n p): R (S m) n (S p)
  | c2 m n p (H: R m n p): R m (S n) (S p)
  | c3 m n p (H: R (S m) (S n) (S (S p))): R m n p
  | c4 m n p (H: R m n p): R n m p.

Example r112:
  R 1 1 2.
Proof.
  apply c2.
  apply c1.
  apply c0.
Qed.

Example R226:
  R 2 2 6.
Proof.
  apply c2.
  apply c1.
  apply c2.
  apply c1.
  (* no applicable constructor at this point*)
  (* the other two don't make progress *)
Abort.

(* no because the same can be achieved by a combination of c2 and c3 *)

(* no because c3 just doesn't make progress towards R 0 0 0, which is the only probable proposition
 that doesn't depend on others *)

Definition fR: nat -> nat -> nat := plus.

Lemma R_0_n_n:
  forall n, R 0 n n.
Proof.
  intros n.
  induction n.
  - apply c0.
  - apply c2.
    apply IHn.
Qed.

Theorem R_equiv_fR:
  forall m n p, R m n p <-> fR m n = p.
Proof.
  intros m n p.
  split.
  - intros H.
    induction H.
    + reflexivity.
    + simpl. f_equal.  apply IHR.
    + unfold fR. rewrite <- plus_n_S_m. f_equal. apply IHR.
    + unfold fR in IHR. simpl in IHR. rewrite <- plus_n_S_m in IHR.
      injection IHR as h0.
      apply h0.
    + rewrite add_commutativity. apply IHR.
  - intros H.
    unfold fR in H.
    generalize dependent n.
    generalize dependent p.
    induction m.
    + intros p n H.
      simpl in H.
      rewrite H.
      apply R_0_n_n.
    + intros p n H.
      rewrite <- H.
      simpl.
      apply c1.
      apply IHm.
      reflexivity.
Qed.

Inductive subseq: list nat -> list nat -> Prop :=
  | sub_empty (xs: list nat): subseq [] xs
  | sub_hd (x: nat) (xs: list nat) (ys: list nat): subseq xs ys -> subseq (x :: xs) (x :: ys)
  | sub_tl (y: nat) (xs: list nat) (ys: list nat): subseq xs ys -> subseq xs (y :: ys).

Theorem subseq_refl:
  forall xs, subseq xs xs.
Proof.
  intros xs.
  induction xs.
  - apply sub_empty.
  - apply sub_hd. apply IHxs.
Qed.

Theorem subseq_app:
  forall xs ys zs, subseq xs ys -> subseq xs (ys ++ zs).
Proof.
  intros xs ys zs H.
  induction H.
  - apply sub_empty.
  - simpl.
    apply sub_hd.
    apply IHsubseq.
  - simpl.
    apply sub_tl.
    apply IHsubseq.
Qed.

Definition tl {t: Type} (xs: list t) :=
  match xs with
  | [] => []
  | _ :: ys => ys
end.

Definition hd {t: Type} (default: t) (xs: list t) :=
  match xs with
  | [] => default
  | x :: _ => x
end.

Lemma subseq_remove_hd:
  forall xs ys, subseq xs ys -> subseq (tl xs) ys.
Proof.
  intros xs ys H.
  induction H.
  - simpl. apply sub_empty.
  - simpl.
    apply sub_tl.
    apply H.
  - apply sub_tl.
    apply IHsubseq.
Qed.

Lemma subseq_in:
  forall x xs ys, subseq (x :: xs) ys -> In x ys.
Proof.
  intros x xs ys H.
  induction ys.
  - inversion H.
  - inversion H.
    + simpl. left. reflexivity.
    + simpl. right. apply IHys. apply H2.
Qed.

Lemma in_subseq:
  forall x xs, In x xs -> subseq [x] xs.
Proof.
  intros x xs H.
  induction xs.
  - inversion H.
  - simpl in H.
    destruct H.
    + rewrite H.
      apply sub_hd. apply sub_empty.
    + apply sub_tl. apply IHxs. apply H.
Qed.

Lemma subseq_hd:
  forall x xs ys, subseq (x :: xs) ys -> subseq xs ys.
Proof.
  intros x xs ys H.
  induction ys.
  - inversion H.
  - inversion H.
    + apply sub_tl.
      apply H1.
    + apply sub_tl.
      apply IHys.
      apply H2.
Qed.

Theorem subseq_trans:
  forall xs ys zs, subseq xs ys -> subseq ys zs -> subseq xs zs.
Proof.
  intros xs ys zs Hxy Hyz.
  generalize dependent xs.
  induction Hyz.
  - intros xs0 Hxy.
    inversion Hxy.
    apply sub_empty.
  - intros xs0 Hxy.
    inversion Hxy.
    + apply sub_empty.
    + apply sub_hd.
      apply IHHyz.
      apply H1.
    + apply sub_tl.
      apply IHHyz.
      apply H1.
  - intros xs0 Hxy.
    apply sub_tl.
    apply IHHyz.
    apply Hxy.
Qed.

Inductive R': nat -> list nat -> Prop :=
  | d0 : R' 0 []
  | d1 x xs (H: R' x xs): R' (S x) (x :: xs)
  | d2 x xs (H: R' (S x) xs): R' x xs.

Example r_2_1_0:
  R' 2 [1;0].
Proof.
  apply d1.
  apply d1.
  apply d0.
Qed.

Example r_1_1_2_1_0:
  R' 1 [1;2;1;0].
Proof.
  apply d2.
  apply d1.
  apply d2.
  apply d2.
  apply d1.
  apply r_2_1_0.
Qed.

Example r_6_3_2_1_0:
  R' 6 [3;2;1;0].
Proof.
  Abort.

Inductive total_relation: nat -> nat -> Prop :=
  | Total (n m : nat): total_relation n m.

Theorem total_relation_is_total:
  forall n m, total_relation n m.
Proof.
  intros n m.
  apply (Total n m).
Qed.

Inductive empty_relation: nat -> nat -> Prop := .

Theorem empty_relation_is_empty:
  forall n m, ~ empty_relation n m.
Proof.
  intros n m H.
  inversion H.
Qed.

Inductive reg_exp (t: Type): Type :=
  | EmptySet
  | EmptyStr
  | Char (c: t)
  | App (r0 r1: reg_exp t)
  | Union (r0 r1: reg_exp t)
  | Star (r: reg_exp t).

Arguments EmptySet {t}.
Arguments EmptyStr {t}.
Arguments Char {t} _.
Arguments App {t} _.
Arguments Union {t} _.
Arguments Star {t} _.

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {t}: list t -> reg_exp t -> Prop :=
  | MEmpty: [] =~ EmptyStr
  | MChar x: [x] =~ (Char x)
  | MApp s0 re0 s1 re1 (H0: s0 =~ re0) (H1: s1 =~ re1): (s0 ++ s1) =~ (App re0 re1)
  | MUnionL s0 re0 re1 (H0: s0 =~ re0): s0 =~ (Union re0 re1)
  | MUnionR s0 re0 re1 (H1: s0 =~ re1): s0 =~ (Union re0 re1)
  | MStar0 re: [] =~ (Star re)
  | MStarApp s0 s1 re (H0: s0 =~ re) (H1: s1 =~ (Star re)): (s0 ++ s1) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1:
  [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2:
  [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_exp3:
  ~ ([1;2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.

Fixpoint reg_exp_of_list {t} (xs: list t) :=
  match xs with
  | [] => EmptyStr
  | x :: xs => App (Char x) (reg_exp_of_list xs)
end.

Example reg_exp_ex4:
  [1;2;3] =~ reg_exp_of_list [1;2;3].
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply (MApp [2]).
    + apply MChar.
    + apply (MApp [3]).
      * apply MChar.
      * apply MEmpty.
Qed.

Lemma MStar1:
  forall t s (re: reg_exp t), s =~ re -> s =~ Star re.
Proof.
  intros t s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

Lemma EmptySet_is_empty:
  forall t (xs: list t), ~ (xs =~ EmptySet).
Proof.
  intros t xs H.
  inversion H.
Qed.

Lemma MUnion':
  forall t (xs: list t) (re0 re1: reg_exp t),
    xs =~ re0 \/ xs =~ re1 -> xs =~ Union re0 re1.
Proof.
  intros t xs re0 re1 H.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar':
  forall t (xss: list (list t)) (re: reg_exp t),
    (forall xs, In xs xss -> xs =~ re) ->
    fold app xss [] =~ Star re.
Proof.
  intros t xss re H.
  induction xss.
  - simpl. apply MStar0.
  - simpl.
    apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHxss.
      intros xs H'.
      apply H.
      simpl.
      right.
      apply H'.
Qed.

Definition EmptyStr' {t: Type} := @Star t EmptySet.

Theorem EmptyStr'_eq_to_EmptyStr:
  forall t (xs: list t),
    xs =~ EmptyStr <-> xs =~ EmptyStr'.
Proof.
  intros t xs.
  split.
  - intros H.
    inversion H.
    + unfold EmptyStr'.
      apply MStar0.
  - intros H.
    unfold EmptyStr' in H.
    inversion H.
    + apply MEmpty.
    + inversion H1.
Qed.

Fixpoint re_chars {t} (re: reg_exp t): list t :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App xs ys => re_chars xs ++ re_chars ys
  | Union xs ys => re_chars xs ++ re_chars ys
  | Star re => re_chars re
end.

Theorem in_re_match:
  forall t (xs: list t) (re: reg_exp t) (x: t),
    xs =~ re -> In x xs -> In x (re_chars re).
Proof.
  intros t xs re x H0 H1.
  induction H0.
  - simpl in H1. destruct H1.
  - simpl. simpl in H1. apply H1.
  - simpl.
    rewrite In_app_iff.
    rewrite In_app_iff in H1.
    destruct H1.
    + left. apply IHexp_match1. apply H.
    + right. apply IHexp_match2. apply H.
  - simpl.
    rewrite In_app_iff.
    left.
    apply IHexp_match.
    apply H1.
  - simpl.
    rewrite In_app_iff.
    right.
    apply IHexp_match.
    apply H1.
  - simpl in H1. destruct H1.
  - simpl.
    rewrite In_app_iff in H1.
    destruct H1.
    + apply IHexp_match1. apply H.
    + simpl in IHexp_match2.
      apply IHexp_match2.
      apply H.
Qed.

Fixpoint re_not_empty {t: Type} (re: reg_exp t): bool :=
  match re with
  | EmptySet => false
  | Union r0 r1 => re_not_empty r0 || re_not_empty r1
  | App r0 r1 => re_not_empty r0 && re_not_empty r1
  | _ => true
end.

Lemma re_not_empty_correct:
  forall t (re: reg_exp t), (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros t re.
  split.
  - intros [s E].
    induction E.
    + reflexivity.
    + reflexivity.
    + simpl.
      rewrite IHE1.
      rewrite IHE2.
      reflexivity.
    + simpl.
      rewrite IHE.
      reflexivity.
    + simpl.
      rewrite IHE.
      destruct (re_not_empty re0).
      * reflexivity.
      * reflexivity.
    + reflexivity.
    + rewrite IHE2. reflexivity.
  - intros H.
    induction re.
    + discriminate H.
    + exists []. apply MEmpty.
    + exists [c]. apply MChar.
    + simpl in H.
      rewrite andb_true_iff in H.
      destruct H.
      apply IHre1 in H.
      apply IHre2 in H0.
      destruct H.
      destruct H0.
      exists (x ++ x0).
      apply MApp.
      * apply H.
      * apply H0.
    + simpl in H.
      rewrite orb_true_iff in H.
      destruct H.
      * apply IHre1 in H.
        destruct H.
        exists x.
        apply MUnionL.
        apply H.
      * apply IHre2 in H.
        destruct H.
        exists x.
        apply MUnionR.
        apply H.
    + exists [].
      apply MStar0.
Qed.

Lemma star_app:
  forall t (xs ys : list t) (re: reg_exp t),
    xs =~ Star re -> ys =~ Star re -> xs ++ ys =~ Star re.
Proof.
  intros t xs ys re H.
  remember (Star re) as re' eqn:Eq.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - intros H'. apply H'.
  - intros H'.
    rewrite <- app_assoc.
    apply MStarApp.
    + apply H.
    + apply IHexp_match2.
      * apply Eq.
      * apply H'.
Qed.

Lemma MStar'':
  forall (t: Type) (xs : list t) (re: reg_exp t),
    xs =~ Star re ->
    exists xss: list (list t),
      xs = fold app xss []
      /\ forall ys, In ys xss -> ys =~ re.
Proof.
  intros t xs re H.
  remember (Star re) as re' eqn:E.
  induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists [].
    split.
    + reflexivity.
    + intros ys H'.
      simpl in H'.
      exfalso.
      apply H'.
  - apply IHexp_match2 in E as E'.
    destruct E' as [xss [xss_concat xss_match]].
    exists (s0 :: xss).
    split.
    + simpl. rewrite xss_concat. reflexivity.
    + intros ys [Hy | Hin].
      * rewrite Hy.
        injection E as E.
        rewrite <- E.
        apply H.
      * apply xss_match.
        apply Hin.
Qed.

Fixpoint pumping_constant {t} (re: reg_exp t): nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re0 re1 =>
      pumping_constant re0 + pumping_constant re1
  | Union re0 re1 =>
      pumping_constant re0 + pumping_constant re1
  | Star r => pumping_constant r
end.

(*
The intiutive idea behind the pumping lemma (with help of ChatGPT):
- even if a regular expression dosen't have Star, it describes a regular language, and the automaton that
recognizes it will have loops, which guarantee the existence of repeatable substrings that can be matched by the regular
expression. Those are the pumpable substrings.
- the surrounding strings xs and zs are there because ys (the pumpable substring) can appear in the middle of the string,
and not necessarily in the begining or end.
- the pumping constant comes from the number of states of the automaton.
*)

Lemma pumping_constant_ge_1:
  forall t (re: reg_exp t), pumping_constant re >= 1.
Proof.
  intros t re.
  induction re.
  - simpl. apply le_n.
  - simpl. apply le_n.
  - simpl. apply le_S. apply le_n.
  - simpl. unfold ge. apply cases_le_plus. left. apply IHre1.
  - simpl. unfold ge. apply cases_le_plus. left. apply IHre1.
  - simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false:
  forall t (re: reg_exp t),
    pumping_constant re = 0 -> False.
Proof.
  intros t re H.
  assert (H': pumping_constant re >= 1).
  - apply pumping_constant_ge_1.
  - rewrite H in H'.
    inversion H'.
Qed.

Fixpoint napp {t} (n: nat) (xs: list t): list t :=
  match n with
  | 0 => []
  | S n' => xs ++ napp n' xs
end.

Lemma napp_plus:
  forall t (n m : nat) (xs: list t),
    napp (n + m) xs = napp n xs ++ napp m xs.
Proof.
  intros t n m xs.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn. rewrite app_assoc. reflexivity.
Qed.

Lemma napp_app_star:
  forall t s0 s1 (re: reg_exp t) m,
    s0 =~ re -> s1 =~ Star re -> napp m (s0 ++ s1) =~ Star re.
Proof.
  intros t s0 s1 re m H0 H1.
  induction m.
  - simpl. apply MStar0.
  - simpl.
    rewrite <- app_assoc.
    apply MStarApp.
    + apply H0.
    + apply star_app.
      * apply H1.
      * apply IHm.
Qed.

Lemma length_at_least_1:
  forall t (xs: list t),
    1 <= length xs -> xs <> [].
Proof.
  intros t xs H.
  unfold not.
  intros H'.
  rewrite H' in H.
  simpl in H.
  inversion H.
Qed.

Lemma weak_pumping:
  forall t (re: reg_exp t) xs,
    xs =~ re ->
    pumping_constant re <= length xs ->
    exists ws ys zs,
      xs = ws ++ ys ++ zs /\
        ys <> [] /\
        forall m, ws ++ napp m ys ++ zs =~ re.
Proof.
  intros t re xs Hre.
  induction Hre.
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H1.
  - simpl.
    rewrite app_length.
    intros H.
    apply plus_le_cases in H.
    destruct H.
    + apply IHHre1 in H.
      destruct H as [ws [ys [zs [s0_app [ys_non_empty ys_repetition]]]]].
      exists ws.
      exists ys.
      exists (zs ++ s1).
      split.
      * rewrite s0_app.
        rewrite <- (app_assoc t ws (ys ++ zs) s1).
        rewrite <- (app_assoc t ys zs s1).
        reflexivity.
      * split.
        -- apply ys_non_empty.
        -- intros m.
           rewrite (app_assoc t ws (napp m ys) (zs ++ s1)).
           rewrite (app_assoc t (ws ++ (napp m ys)) zs s1).
           rewrite <- (app_assoc t ws (napp m ys) zs).
           apply (MApp (ws ++ napp m ys ++ zs) re0 s1 re1).
           ++ apply ys_repetition.
           ++ apply Hre2.
   + apply IHHre2 in H.
     destruct H as [ws [ys [zs [s1_app [ys_non_empty ys_repetition]]]]].
     exists (s0 ++ ws).
     exists ys.
     exists zs.
     split.
     * rewrite <- (app_assoc t s0  ws (ys ++ zs)).
       rewrite s1_app.
       reflexivity.
     * split.
       -- apply ys_non_empty.
       -- intros m.
          rewrite <- (app_assoc t s0 ws (napp m ys ++ zs)).
          apply (MApp s0 re0 (ws ++ napp m ys ++ zs) re1).
          ++ apply Hre1.
          ++ apply ys_repetition.
  - simpl.
    intros H.
    apply plus_le in H.
    destruct H.
    apply IHHre in H.
    destruct H as [ws [ys [zs [s0_app [ys_non_empty ys_repetition]]]]].
    exists ws.
    exists ys.
    exists zs.
    split.
    + apply s0_app.
    + split.
      * apply ys_non_empty.
      * intros m.
        apply MUnionL.
        apply ys_repetition.
  - simpl.
    intros H.
    apply plus_le in H.
    destruct H.
    apply IHHre in H0.
    destruct H0 as [ws [ys [zs [s0_app [ys_non_empty ys_repetition]]]]].
    exists ws.
    exists ys.
    exists zs.
    split.
    + apply s0_app.
    + split.
      * apply ys_non_empty.
      * intros m.
        apply MUnionR.
        apply ys_repetition.
  - simpl.
    intros H.
    assert (H1: 1 <= pumping_constant re).
    + apply pumping_constant_ge_1.
    + assert (Hf: pumping_constant re <= 0 -> False).
      * intros _.
        apply (le_trans 1 (pumping_constant re) 0 H1) in H.
        inversion H.
      * exfalso.
        apply Hf.
        apply H.
  - intros H.
    simpl in IHHre2.
    exists [].
    exists (s0 ++ s1).
    exists [].
    split.
    + simpl. rewrite app_nil_r. reflexivity.
    + split.
      * apply (le_trans 1 _ (length (s0 ++ s1))) in H.
        apply length_at_least_1.
        apply H.
        apply pumping_constant_ge_1.
      * intros m.
        simpl.
        rewrite app_nil_r.
        apply (napp_app_star t s0 s1 re m Hre1 Hre2).
Qed.

Theorem and_le_plus:
  forall m n p q, m <= p /\ n <= q -> m + n <= p + q.
Proof.
  intros m n p q [H0 H1].
  apply (plus_le_compat_r _ _ n) in H0.
  apply (plus_le_compat_l _ _ p) in H1.
  apply (le_trans (m + n) (p + n) (p + q) H0 H1).
Qed.

Lemma pumping:
  forall t (re: reg_exp t) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists xs ys zs,
      s = xs ++ ys ++ zs /\
      ys <> [] /\
      length xs + length ys <= pumping_constant re /\
      forall m, xs ++ napp m ys ++ zs =~ re.
Proof.
  intros t re s H.
  induction H.
  - simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H1.
  - simpl.
    rewrite app_length.
    intros H'.
    apply plus_le_cases in H' as H3.
    destruct H3.
    + apply IHexp_match1 in H1.
      destruct H1 as [xs [ys [zs [s0_app [ys_non_empty [xs_ys_length napp_re0]]]]]].
      exists xs.
      exists ys.
      exists (zs ++ s1).
      rewrite s0_app.
      split.
      * rewrite <- (app_assoc _ xs  _ _).
        rewrite <- (app_assoc _ ys zs s1).
        reflexivity.
      * split.
        -- apply ys_non_empty.
        -- split.
           ++ apply (le_plus_trans _ _ (pumping_constant re1)).
              apply xs_ys_length.
           ++ intros m.
              rewrite app_assoc.
              rewrite (app_assoc _ (xs ++ napp m ys) _ _).
              rewrite <- (app_assoc _ xs (napp m ys) zs).
              apply (MApp _ _ _ _).
              ** apply napp_re0.
              ** apply H0.
   + apply IHexp_match2 in H1 as H2.
     destruct H2 as [xs [ys [zs [s1_app [ys_non_empty [xs_ys_length napp_re1]]]]]].
     exists (s0 ++ xs).
     exists ys.
     exists zs.
     split.
     * rewrite s1_app.
       rewrite <- app_assoc.
       reflexivity.
     * split.
       -- apply ys_non_empty.
       -- split.
          ++ rewrite app_length.
             rewrite <- add_assoc.
             apply le_trans with (n := length s0 + length s1).
             ** rewrite <- app_length.
                rewrite <- app_length.
                rewrite <- app_length.
                rewrite s1_app.
                admit.
             **
                admit.
          ++ intros m.
             rewrite <- app_assoc.
             apply MApp.
             ** apply H.
             ** apply napp_re1.
  - simpl.
    intros H2.
    apply plus_le in H2.
    destruct H2.
    apply IHexp_match in H0.
    destruct H0 as [xs [ys [zs [s0_app [ys_non_empty [xs_ys_length napp_re0]]]]]].
    exists xs.
    exists ys.
    exists zs.
    split.
    + apply s0_app.
    + split.
      * apply ys_non_empty.
      * split.
        -- apply cases_le_plus.
           left.
           apply xs_ys_length.
        -- intros m.
           apply MUnionL.
           apply napp_re0.
  - simpl.
    intros H2.
    apply plus_le in H2.
    destruct H2.
    apply IHexp_match in H1.
    destruct H1 as [xs [ys [zs [s0_app [ys_non_empty [xs_ys_length napp_re1]]]]]].
    exists xs.
    exists ys.
    exists zs.
    split.
    + apply s0_app.
    + split.
      * apply ys_non_empty.
      * split.
        -- apply cases_le_plus.
           right.
           apply xs_ys_length.
        -- intros m.
           apply MUnionR.
           apply napp_re1.
  - simpl.
    intros H2.
    inversion H2.
    exfalso.
    apply (pumping_constant_0_false t re).
    apply H1.
  - simpl.
    rewrite app_length.
    intros H1.
    exists [].
    exists (s0 ++ s1).
    exists [].
    split.
    + simpl. rewrite app_nil_r. reflexivity.
    + split.
      * apply (le_trans 1 _ (length s0 + length s1)) in H1.
        apply length_at_least_1.
        rewrite app_length.
        apply H1.
        apply pumping_constant_ge_1.
      * split.
        -- simpl.
           rewrite app_length.

           admit.
        -- intros m.
           simpl.
           rewrite app_nil_r.
           apply (napp_app_star t s0 s1 re m H H0).
Admitted.


Theorem filter_non_empty_In:
  forall n xs, filter (fun x => n =? x) xs <> [] -> In n xs.
Proof.
  intros n xs.
  induction xs.
  - intros H.
    apply H.
    reflexivity.
  - simpl.
    destruct (n =? x) eqn:E.
    + intros H.
      rewrite eqb_eq in E.
      rewrite E.
      left.
      reflexivity.
    + intros H.
      right.
      apply IHxs.
      apply H.
Qed.

Inductive reflect (p: Prop): bool -> Prop :=
| ReflectT (H: p): reflect p true
| ReflectF (H: ~p): reflect p false.

Theorem iff_reflect:
  forall p b, (p  <->  b = true) -> reflect p b.
Proof.
  intros p b H.
  destruct b eqn:E.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

Theorem reflect_iff:
  forall p b, reflect p b -> (p <-> b = true).
Proof.
  intros p b H.
  inversion H.
  - split.
    + intros _. reflexivity.
    + intros _. apply H0.
  - split.
    + intros H'. exfalso. apply H0. apply H'.
    + intros H'. discriminate.
Qed.

Lemma eqbP:
  forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m.
  apply iff_reflect.
  rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In':
  forall n xs,
    filter (fun x => n =? x) xs <> [] -> In n xs.
Proof.
  intros n xs.
  induction xs.
  - simpl. intros H. apply H. reflexivity.
  - simpl.
    destruct (eqbP n x) as [E | F].
    + intros _. rewrite E. left. reflexivity.
    + intros H'. right. apply IHxs. apply H'.
Qed.

Fixpoint count n xs :=
  match xs with
  | [] => 0
  | y :: ys => (if n =? y then 1 else 0) + count n ys
end.

Theorem eqbP_practice:
  forall n xs, count n xs = 0 -> ~(In n xs).
Proof.
  intros n xs H H'.
  induction xs.
  - inversion H'.
  - simpl in H.
    destruct (eqbP n x) as [E | F].
    + discriminate.
    + apply IHxs.
      * simpl in H. apply H.
      * simpl in H'.
        destruct H'.
        -- rewrite H0 in F.
           exfalso.
           apply F.
           reflexivity.
        -- apply H0.
Qed.

Lemma plus_eq_0:
  forall n m, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  induction n.
  - split.
    + reflexivity.
    + simpl in H. apply H.
  - discriminate H.
Qed.

Theorem eqbP_practice':
  forall n xs, count n xs = 0 -> ~(In n xs).
Proof.
  intros n xs H.
  induction xs.
  - simpl. apply not_false.
  - simpl. intros H'.
    destruct H'.
    + rewrite H0 in H.
      simpl in H.
      rewrite eqb_refl in H.
      discriminate H.
    + apply IHxs.
      * simpl in H.
        apply plus_eq_0 in H.
        apply H.
      * apply H0.
Qed.

Inductive nostutter {t: Type}: list t -> Prop :=
  | nostutter_empty (xs: list t): xs = [] -> nostutter xs
  | nostutter_singleton (x: t): nostutter [x]
  | nostutter_consecutive (x y: t) (xs: list t): x <> y -> nostutter (y :: xs) -> nostutter (x :: y :: xs).

Example test_nostutter_1:
  nostutter [3;1;4;1;5;6].
Proof.
  apply nostutter_consecutive.
  intro H. discriminate.
  apply nostutter_consecutive.
  intro H. discriminate.
  apply nostutter_consecutive.
  intro H. discriminate.
  apply nostutter_consecutive.
  intro H. discriminate.
  apply nostutter_consecutive.
  intro H. discriminate.
  apply nostutter_singleton.
Qed.

Example testn_nostutter_2:
  nostutter (@nil nat).
Proof.
  apply nostutter_empty.
  reflexivity.
Qed.

Example test_nostutter_3:
  nostutter [5].
Proof.
  apply nostutter_singleton.
Qed.

Example test_nostutter_4:
  ~ nostutter [3;1;1;4].
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  (* contradiction; auto. Qed. *)
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - apply H1. reflexivity.
Qed.

Inductive merge {t: Type}: list t -> list t -> list t -> Prop :=
  | merge_empty: merge [] [] []
  | merge_xs (x: t) (xs ys ms: list t): merge xs ys ms -> merge (x :: xs) ys (x :: ms)
  | merge_ys (y: t) (xs ys ms: list t): merge xs ys ms -> merge xs (y :: ys) (y :: ms).

Theorem merge_filter:
  forall (t: Set) (test: t -> bool) (xs ys ms: list t),
    merge xs ys ms ->
    All (fun n => test n = true) xs ->
    All (fun n => test n = false) ys ->
    filter test ms = xs.
Proof.
  intros t test xs ys ms Hm Ht Hf.
  induction Hm.
  - reflexivity.
  - simpl.
    destruct (test x) eqn:E.
    + simpl in Ht.
      destruct Ht.
      assert (H': filter test ms = xs).
      * apply IHHm.
        apply H0.
        apply Hf.
      * rewrite H'.
        reflexivity.
   + simpl in Ht.
     rewrite E in Ht.
     destruct Ht.
     discriminate.
  - simpl.
    destruct (test y) eqn:E.
    + simpl in Hf.
      destruct Hf.
      rewrite E in H.
      discriminate.
    + simpl in Hf.
      destruct Hf.
      apply IHHm.
      apply Ht.
      apply H0.
Qed.

(*
A different way to characterize the behavior of filter goes like this:
Among all subsequences of l with the property that test evaluates to true on all their members,
filter test l is the longest. Formalize this claim and prove it.
*)

Inductive pal {t: Type}: list t -> Prop :=
  | pal_empty: pal []
  | pal_single (x: t): pal [x]
  | pal_hd (x: t) (xs: list t): pal xs -> pal (x :: xs ++ [x]).

Theorem pal_app_rev:
  forall (t: Type) (xs: list t),
    pal (xs ++ (rev xs)).
Proof.
  intros t xs.
  induction xs.
  - simpl. apply pal_empty.
  - simpl.
    rewrite app_assoc.
    apply (pal_hd x (xs ++ rev xs)).
    apply IHxs.
Qed.

Theorem pal_rev:
  forall (t: Type) (xs: list t),
    pal xs -> xs = rev xs.
Proof.
  intros t xs H.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite <- IHpal.
    reflexivity.
Qed.

Theorem palindrome_converse:
  forall (t: Type) (xs: list t),
    xs = rev xs -> pal xs.
Proof.
  intros t xs H.
  Admitted.

Inductive disjoint {t: Type}: list t -> list t -> Prop :=
  | disjoint_empty: disjoint [] []
  | disjoint_hd (x y:t) (xs ys: list t): x <> y -> ~In x ys -> ~ In y xs -> disjoint (x :: xs) (y :: ys).

Inductive NoDup {t: Type}: list t -> Prop :=
  | nodup_empty: NoDup []
  | nodup_hd (x: t) (xs: list t): ~ In x xs -> NoDup (x :: xs).

(*
Finally, state and prove one or more interesting theorems relating disjoint, NoDup and ++ (list append).
 *)

Lemma in_split:
  forall (t: Type) (x: t) (xs: list t),
    In x xs -> exists ys zs, xs = ys ++ x :: zs.
Proof.
  intros t x xs H.
  induction xs.
  - inversion H.
  - simpl in H.
    destruct H.
    + rewrite H.
      exists [].
      exists xs.
      reflexivity.
    + apply IHxs in H.
      destruct H as [ys [zs H]].
      rewrite H.
      exists (x0 :: ys).
      exists zs.
      reflexivity.
Qed.

Inductive repeats {t: Type}: list t -> Prop :=
  | repeats_hd (x: t) (xs: list t): In x xs -> repeats (x :: xs).

Theorem pigeonghole_principle:
  forall (t: Type) (labels assigned_labels: list t),
    (forall x, In x assigned_labels -> In x labels) ->
    length labels < length assigned_labels -> repeats assigned_labels.
Proof.
  intros t labels assigned_labels.
  induction assigned_labels.
  - intros H H'.
    simpl in H'.
    inversion H'.
  - intros all_in_labels len.
Admitted.

From Stdlib Require Import Strings.Ascii.


Definition string := list ascii.

Lemma provable_equiv_true:
  forall (p: Prop), p -> (p <-> True).
Proof.
  intros p H.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

Lemma not_equiv_false:
  forall (p: Prop), ~p -> (p <-> False).
Proof.
  intros p H.
  split.
  - intros. apply H. apply H0.
  - intros. destruct H0.
Qed.

Lemma null_matches_none:
  forall (xs: string), xs =~ EmptySet <-> False.
Proof.
  intros.
  split.
  - intros.
    inversion H.
  - intros.
    destruct H.
Qed.

Lemma empty_matches_empty_string:
  forall (xs: string), xs =~ EmptyStr <-> xs = [].
Proof.
  intros.
  split.
  - intros.
    inversion H.
    reflexivity.
  - intros.
    rewrite H.
    apply MEmpty.
Qed.

Lemma empty_nomatch_non_empty:
  forall (x: ascii) xs, (x :: xs =~ EmptyStr) <-> False.
Proof.
  intros.
  split.
  - intros.
    inversion H.
  - intros.
    destruct H.
Qed.

Lemma char_nomatch_char:
  forall (x y: ascii) xs, x <> y -> (x :: xs =~ Char y <-> False).
Proof.
  intros.
  split.
  -  intros.
     inversion H0.
     rewrite H4 in H.
     apply H.
     reflexivity.
  - intros.
    destruct H0.
Qed.

Lemma char_eps_suffix:
  forall (x : ascii) xs,
    x :: xs =~ Char x  <->  xs = [].
Proof.
  intros.
  split.
  - intros.
    inversion H.
    reflexivity.
  - intros.
    rewrite H.
    apply MChar.
Qed.

Lemma app_exists:
  forall (xs: string) re0 re1,
    xs =~ App re0 re1  <->  exists ys zs, xs = ys ++ zs /\ ys =~ re0 /\ zs =~ re1.
Proof.
  intros.
  split.
  - intros.
    inversion H.
    exists s0, s1.
    split.
    + reflexivity.
    + split. apply H3. apply H4.
  - intros [ys [zs [H0 [H1 H2]]]].
    rewrite H0.
    apply MApp.
    apply H1.
    apply H2.
Qed.

Lemma app_ne:
  forall (x: ascii) xs re0 re1,
    x :: xs =~ (App re0 re1) <-> ([] =~ re0 /\ x :: xs =~ re1) \/ (exists s0 s1, xs = s0 ++ s1  /\  x :: s0 =~ re0  /\  s1 =~ re1).
Proof.
  intros.
  split.
  - intros.
    inversion H.
    destruct s0 eqn:E.
    + left.
      simpl.
      split.
      * apply H3.
      * apply H4.
    + right.
      exists l, s1.
      injection H0 as H0.
      split.
      * rewrite <- H5.
        reflexivity.
      * split.
        rewrite <- H0.
        apply H3.
        apply H4.
  - intros.
    destruct H.
    + destruct H.
      apply (MApp [] re0 (x :: xs) re1).
      * apply H.
      * apply H0.
    + destruct H as [s0 [s1 [h0 [h1 h2]]]].
      rewrite h0.
      assert (cons_app: (x :: s0) ++ s1 = x :: s0 ++ s1).
      * simpl. reflexivity.
      * rewrite <- cons_app.
        apply (MApp (x :: s0) re0 s1 re1 h1 h2).
Qed.

Lemma union_disj:
  forall (xs: string) re0 re1,
    xs =~ Union re0 re1  <->  xs =~ re0  \/  xs =~ re1.
Proof.
  intros.
  split.
  - intros.
    inversion H.
    + left. apply H2.
    + right. apply H2.
  - intros.
    destruct H.
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

Lemma star_ne:
  forall (x: ascii) xs re,
    x :: xs =~ Star re  <->   exists s0 s1, xs = s0 ++ s1  /\  x :: s0 =~ re  /\  s1 =~ Star re.
Proof.
  intros.
  split.
  - intros.
    remember (Star re) as re' eqn:E.
    inversion H.
    induction H.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + rewrite E in H3.
      discriminate.
    + rewrite E in H2.
      discriminate.
    + rewrite E in H2.
      discriminate.
    + rewrite E in H3.
      injection H3 as H3.
      exists [], xs.
      split.
      * reflexivity.
      *
        (* maybe s0 = [x] s1 = xs *)
        admit.
  - intros.
    destruct H as [s0 [s1 [h0 [h1 h2]]]].
    rewrite h0.
    assert (H': (x :: s0) ++ s1 = x :: s0 ++ s1).
    + simpl. reflexivity.
    + rewrite <- H'.
      apply (MStarApp (x :: s0) s1 re h1 h2).
Admitted.

Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([] =~ re) (m re).

Fixpoint match_eps (re: reg_exp ascii): bool :=
  match re with
  | EmptyStr
  | Star _ => true
  | Union l r => match_eps l || match_eps r
  | App xs ys => match_eps xs && match_eps ys
  | _ => false
end.

Lemma match_ps_refl:
  refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps.
  intros.
  induction re.
  - simpl.
    apply ReflectF.
    unfold not.
    intros.
    inversion H.
  - simpl.
    apply ReflectT.
    apply MEmpty.
  - simpl.
    apply ReflectF.
    unfold not.
    intros.
    inversion H.
  - simpl.
    inversion IHre1.
    + inversion IHre2.
      * simpl.
        apply ReflectT.
        apply (MApp [] re1 [] re2 H0 H2).
      * simpl.
        apply ReflectF.
        unfold not.
        intros.
        inversion H3.
        destruct s1.
        -- apply H2. apply H8.
        -- destruct s0. discriminate. discriminate.
    + simpl.
      apply ReflectF.
      unfold not.
      intros.
      inversion H1.
      destruct s0.
      * apply H0. apply H5.
      * destruct s1. discriminate. discriminate.
  - simpl.
    inversion IHre1.
    + apply ReflectT.
      apply (MUnionL [] re1 re2 H0).
    + simpl.
      inversion IHre2.
      * apply ReflectT.
        apply (MUnionR [] re1 re2 H2).
      * apply ReflectF.
        unfold not.
        intros.
        inversion H3.
        -- apply H0.  apply H6.
        -- apply H2.  apply H6.
  - simpl.
    apply ReflectT.
    apply MStar0.
Qed.

Definition is_der re (x: ascii) re' :=
  forall xs, x :: xs =~ re  <->  xs =~ re'.

Definition derives d :=
  forall x re, is_der re x (d x re).
