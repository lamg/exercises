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

Theorem subseq_trans:
  forall xs ys zs, subseq xs ys -> subseq ys zs -> subseq xs zs.
Proof.
  intros xs ys zs H.
  generalize dependent zs.
  induction H.
  - intros zs H'. apply sub_empty.
  - intros zs H'.
    inversion H'.
    + apply sub_hd. apply IHsubseq. apply H3.
    + apply sub_tl. Admitted.

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
