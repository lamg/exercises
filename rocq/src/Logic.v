Require Export Rocq.Basics.
Require Export Rocq.Poly.
Require Export Rocq.Tactics.
(* Check (forall n m : nat, n + m = m + n) : Prop. *)

(* Check (2 = 2) : Prop. *)
Definition plus_claim: Prop := 2 + 2 = 4.

Theorem plus_claim_is_true:
  plus_claim.
Proof. reflexivity. Qed.

Definition is_three (n: nat) := n = 3.

Definition injective {t u} (f: t -> u) : Prop :=
  forall x y: t, f x = f y -> x = y.

Lemma succ_inj:
  injective S.
Proof.
  intros x y H.
  injection H as H0.
  apply H0.
Qed.

Example and_example:
  3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Example and_example':
  3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - reflexivity.
  - reflexivity.
Qed.

Example plus_is_0:
  forall n m: nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m eq.
  destruct n eqn:E.
  - simpl in eq.
    split.
    + reflexivity.
    + apply eq.
  - discriminate eq.
Qed.

Lemma and_example2:
  forall n m : nat,
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [c0 c1].
  rewrite c0.
  rewrite c1.
  reflexivity.
Qed.

Lemma and_example2'':
  forall n m: nat,
    n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m h0 h1.
  rewrite h0.
  rewrite h1.
  reflexivity.
Qed.

Lemma proj1:
  forall p q : Prop, p /\ q -> p.
Proof.
  intros p q h.
  destruct h as [h0 _].
  apply h0.
Qed.

Lemma proj2:
  forall p q : Prop, p /\ q -> q.
Proof.
  intros p q h.
  destruct h as [_ h1].
  apply h1.
Qed.

Theorem and_commutativity:
  forall p q: Prop, p /\ q -> q /\ p.
Proof.
  intros p q [hp hq].
  split.
  - apply hq.
  - apply hp.
Qed.

Theorem and_assoc:
  forall p q r: Prop,
    p /\ (q /\ r) -> (p /\ q) /\ r.
Proof.
  intros p q r [hp [hq hr]].
  split.
  - split.
    + apply hp.
    + apply hq.
  - apply hr.
Qed.

Lemma factor_is_0:
  forall n m : nat,
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [hn | hm].
  - rewrite hn.
    reflexivity.
  - rewrite hm.
    apply NatPlayground.mult_n_0.
Qed.

Lemma or_intro_l:
  forall p q: Prop, p -> p \/ q.
Proof.
  intros p q hp.
  left.
  apply hp.
Qed.

Lemma zero_or_succ:
  forall n: nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_is_0:
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m h.
  destruct n eqn:E.
  - left. reflexivity.
  - right.
    simpl in h.
    apply plus_is_0 in h.
    apply proj1 in h.
    apply h.
Qed.

Lemma or_commutativity:
  forall p q: Prop, p \/ q -> q \/ p.
Proof.
  intros p q [hp | hq].
  - right. apply hp.
  - left. apply hq.
Qed.



Theorem ex_falso_quodlibet:
  forall p, False -> p.
Proof.
  intros p contra.
  destruct contra.
Qed.

Theorem not_implies_our_not:
  forall p, ~p -> (forall q:Prop, p -> q).
Proof.
  intros p notp q cond.
  (* notp: ~p
     cond: p
     q *)
  apply ex_falso_quodlibet.
  (* False *)
  unfold not in notp.
  (* notp: p -> False *)
  apply notp.
  (* p *)
  apply cond.
Qed.

Theorem zero_not_one:
  0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_false:
  ~ False.
Proof.
  unfold not.
  intros cond.
  apply cond.
Qed.

Theorem contradiction_implies_anything:
  forall p q: Prop, p /\ ~p -> q.
Proof.
  intros p q.
  apply not_implies_our_not.
  unfold not.
  intros cond.
  destruct cond as [c0 c1].
  apply c1.
  apply c0.
Qed.

Theorem double_neg:
  forall p, p -> ~~p.
Proof.
  intros p cond.
  unfold not.
  intros q.
  apply q.
  apply cond.
Qed.

Theorem de_morgan_not_or:
  forall p q, ~(p \/ q) -> ~p /\ ~q.
Proof.
  unfold not.
  intros p q cond.
  (*cond: p \/ q -> False *)
  (*(p -> False) /\ (q -> False)*)
  split.
  - (* p -> False *)
    intro H.
    (* H: p *)
    (* False *)
    apply cond.
    (* p \/ q *)
    left.
    (* p *)
    apply H.
  - intro H.
    apply cond.
    right.
    apply H.
Qed.

Lemma not_S_pred_n:
  ~(forall n, S (pred n) = n).
Proof.
  unfold not.
  intros H.
  assert (E: S (pred 0) = 0).
  - apply H.
  - discriminate E.
Qed.

Theorem not_true_is_false:
  forall b, b <> true -> b = false.
Proof.
  intros b cond.
  destruct b eqn:E.
  - apply ex_falso_quodlibet.
    apply cond.
    reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false':
  forall b, b <> true -> b = false.
Proof.
  intros [] H.
  - exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Lemma true_is_true:
  True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) :=
  match n with
  | 0 => True
  | S _ => False
end.

Theorem disc_example:
  forall n, ~(0 = S n).
Proof.
  intros n contra.
  assert (H: disc_fn 0).
  - simpl. apply I.
  - rewrite contra in H.
    simpl in H.
    apply H.
Qed.

Definition disc_nil {t: Type} (xs : list t) :=
  match xs with
  | nil => True
  | _  => False
end.

Theorem nil_is_not_cons:
  forall t (x: t) (xs: list t),
    ~(nil = x :: xs).
Proof.
  intros t x xs contra.
  assert (H: @disc_nil t nil).
  - simpl. apply I.
  - rewrite contra in H.
    simpl in H.
    apply H.
Qed.

Theorem iff_sym:
  forall p q, (p <-> q) -> (q <-> p).
Proof.
  intros p q [hl hr].
  split.
  - apply hr.
  - apply hl.
Qed.

Lemma not_true_iff_false:
  forall b, b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros h.
    rewrite h.
    intros contra.
    discriminate contra.
Qed.

Lemma apply_iff_example:
  forall p q r, (p <-> q) -> (q -> r) -> (p -> r).
Proof.
  intros p q r eq h0 h1.
  apply h0.
  apply eq.
  apply h1.
Qed.

Theorem iff_refl:
  forall p, p <-> p.
Proof.
  intros p.
  split.
  - intros h. apply h.
  - intros h. apply h.
Qed.

Theorem iff_trans:
  forall p q r, (p <-> q) -> (q <-> r) -> (p <-> r).
Proof.
  intros p q r [h0 h1] [i0 i1].
  split.
  - intro hp.
    apply i0.
    apply h0.
    apply hp.
  - intro hr.
    apply h1.
    apply i1.
    apply hr.
Qed.

Lemma or_intro_r:
  forall p q, p -> q \/ p.
Proof.
  intros p q h.
  right.
  apply h.
Qed.


Theorem or_distributes_over_and:
  forall p q r, p \/ (q /\ r) <-> (p \/ q) /\ (p \/ r).
Proof.
  intros p q r.
  split.
  - intros [h0 | [h1 h2]].
    split.
    + apply or_intro_l.
      apply h0.
    + apply or_intro_l.
      apply h0.
    + split.
      * apply or_intro_r.
        apply h1.
      * apply or_intro_r.
        apply h2.
  - intros [[h0|h1] [h2|h3]].
    + apply or_intro_l.
      apply h0.
    + apply or_intro_l.
      apply h0.
    + apply or_intro_l.
      apply h2.
    + apply or_intro_r.
      split.
      * apply h1.
      * apply h3.
Qed.

From Stdlib Require Import Setoids.Setoid.

Lemma mul_eq_0:
  forall n m, n * m = 0  <->  n = 0 \/ m = 0.
Proof.
  intros n m.
  split.
  - apply mult_is_0.
  - apply factor_is_0.
Qed.

Theorem or_assoc:
  forall p q r, p \/ (q \/ r) <-> (p \/ q) \/ r.
Proof.
  intros p q r.
  split.
  - intros [ h0 | [h1 | h2] ].
    + left.
      left.
      apply h0.
    + left.
      right.
      apply h1.
    + right.
      apply h2.
  - intros [ [h0 | h1] | h2 ].
    + left.
      apply h0.
    + right.
      left.
      apply h1.
    + right.
      right.
      apply h2.
Qed.

Lemma mul_eq_0_ternary:
  forall m n p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros m n p.
  rewrite mul_eq_0 with (n := n * m).
  rewrite mul_eq_0.
  symmetry.
  apply or_assoc.
Qed.

Definition Even x := exists n, x = double n.

Lemma four_is_Even: Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2:
  forall n, (exists m, n = 4 + m) -> (exists p, n = 2 + p).
Proof.
  intros n [m h].
  exists (2 + m).
  apply h.
Qed.

Theorem dist_not_exists:
  forall (t: Type) (p: t -> Prop),
    (forall x, p x) -> ~(exists x, ~ p x).
Proof.
  intros t p h e.
  destruct e as [x E].
  apply E.
  apply h.
Qed.

Theorem dist_exists_or:
  forall (t: Type) (p q: t -> Prop),
    (exists x, p x \/ q x) <-> (exists x, p x) \/ (exists x, q x).
Proof.
  intros t p q.
  split.
  - intros h.
    destruct h as [x E].
    destruct E as [h0 | h1].
    + left.
      exists x.
      apply h0.
    + right.
      exists x.
      apply h1.
  - intros [h0 | h1].
    + destruct h0 as [x E].
      exists x.
      left.
      apply E.
    + destruct h1 as [x E].
      exists x.
      right.
      apply E.
Qed.

Theorem leb_plus_exists:
  forall n m: nat, n <=? m = true -> exists x, m = n + x.
Proof.
  intros n m h.
  generalize dependent m.
  induction n as [|n' ind].
  - intros m.
    exists m.
    reflexivity.
  - intros m h.
    destruct m eqn:F.
    + discriminate h.
    + simpl.
      simpl in h.
      apply ind in h.
      destruct h as [y E].
      exists y.
      f_equal.
      apply E.
Qed.

Theorem plus_exists_leb:
  forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n.
  induction n as [|n' ind].
  - intros m h.
    reflexivity.
  - intros m h.
    destruct h as [x E].
    rewrite E.
    simpl.
    apply ind.
    exists x.
    reflexivity.
Qed.

Fixpoint In {t: Type} (x : t) (xs : list t) :=
  match xs with
  | [] => False
  | y :: ys => x = y  \/  In x ys
end.

Example In_example:
  In 4 [1; 2 ; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2:
  forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [ h | [h | []] ].
  - exists 1. rewrite h. reflexivity.
  - exists 2. rewrite h. reflexivity.
Qed.

Theorem In_map:
  forall (t u: Type) (f: t -> u) (xs: list t) (x: t),
    In x xs -> In (f x) (map f xs).
Proof.
  intros t u f xs x.
  induction xs as [|y ys ind].
  - simpl. intros [].
  - simpl.
    intros [H | G].
    + left.
      f_equal.
      apply H.
    + right.
      apply ind.
      apply G.
Qed.

Theorem In_map_iff:
  forall (t u : Type) (f: t -> u) (xs: list t) (y: u),
    In y (map f xs) <-> exists x, f x = y  /\  In x xs.
Proof.
  intros t u f xs y.
  split.
  induction xs as [|x' xs' ind].
  - intros [].
  - simpl.
    intros [h0 | h1].
    + exists x'.
      split.
      * rewrite h0. reflexivity.
      * left. reflexivity.
    + apply ind in h1.
      destruct h1 as [x E].
      exists x.
      split.
      * apply E.
      * right.
        apply E.
  - intros h.
    destruct h as [x [E F]].
    rewrite <- E.
    apply In_map.
    apply F.
Qed.

Theorem In_app_iff:
  forall t xs ys (x: t),
    In x (xs ++ ys) <-> In x xs \/ In x ys.
Proof.
  intros t xs.
  induction xs as [|x' xs' ind].
  - simpl.
    split.
    + intros h.
      right.
      apply h.
    + intros [h0 | h1].
      * exfalso. apply h0.
      * apply h1.
  - split.
    + simpl.
      intros [h0 | h1].
      * left. left.  apply h0.
      * rewrite ind in h1.
        rewrite <- or_assoc.
        right.
        apply h1.
    + intros [h0 | h1].
      * simpl.
        simpl in h0.
        rewrite ind.
        rewrite or_assoc.
        left.
        apply h0.
      * simpl.
        rewrite ind.
        right.
        right.
        apply h1.
Qed.

Fixpoint All {t : Type} (p: t -> Prop) (xs: list t) :=
  match xs with
  | [] => True
  | y :: ys => p y /\ All p ys
end.

Theorem All_In:
  forall t (p: t -> Prop) (xs: list t),
    (forall x, In x xs -> p x) <-> All p xs.
Proof.
  intros t p xs.
  induction xs as [|y ys ind].
  - simpl.
    split.
    + intros h. apply I.
    + intros h x f.
      exfalso.
      apply f.
  - simpl.
    split.
  + intros h.
    rewrite <- ind.
    split.
    * apply h. left. reflexivity.
    * intros x h'.
      apply h.
      right.
      apply h'.
  + intros [h0 h1] x [m0 | m1].
    * rewrite m0. apply h0.
    * rewrite <- ind in h1.
      apply h1 in m1.
      apply m1.
Qed.

Definition combine_odd_even (Podd Peven: nat -> Prop) :=
  fun n => if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro:
  forall (Podd Peven: nat -> Prop) (n: nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n h0 h1.
  destruct (odd n) eqn:E.
  - unfold combine_odd_even.
    rewrite E.
    apply h0.
    reflexivity.
  - unfold combine_odd_even.
    rewrite E.
    apply h1.
    reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
  forall (Podd Peven : nat -> Prop) (n: nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n h0 h1.
  unfold combine_odd_even in h0.
  rewrite h1 in h0.
  apply h0.
Qed.

Theorem combine_odd_even_elim_even:
  forall (Podd Peven: nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros Podd Peven n h0 h1.
  unfold combine_odd_even in h0.
  rewrite h1 in h0.
  apply h0.
Qed.

Lemma add_comm3_take3:
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (Induction.add_commutativity y z).
  rewrite Induction.add_commutativity.
  reflexivity.
Qed.

Theorem in_not_nil:
  forall t (x: t) (xs: list t),
    In x xs -> xs <> [].
Proof.
  intros t x xs h.
  unfold not.
  intro h'.
  rewrite h' in h.
  simpl in h.
  apply h.
Qed.

Lemma in_not_nil_42:
  forall xs: list nat, In 42 xs -> xs <> [].
Proof.
  intros xs h.
  apply (in_not_nil _ _ _ h).
Qed.

Example even_42_bool: even 42 = true. reflexivity. Qed.

Example even_42_prop: Even 42. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double:
  forall k, even (double k) = true.
Proof.
  intros k.
  induction k as [|k' ind].
  - reflexivity.
  - simpl.
    apply ind.
Qed.

Import NatPlayground.

Lemma even_double_conv:
  forall n, exists k, n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [|n' ind].
  - exists 0. reflexivity.
  - destruct ind as [k E].
    destruct (even n') eqn:F.
    + rewrite Induction.even_succ.
      exists k.
      rewrite F.
      simpl.
      rewrite E.
      reflexivity.
    + rewrite Induction.even_succ.
      rewrite F.
      simpl.
      rewrite E.
      exists (S k).
      simpl.
      reflexivity.
Qed.

Lemma even_bool_prop:
  forall n, even n = true <-> Even n.
Proof.
  intros n.
  split.
  - intros h.
    destruct (even_double_conv n) as [k E].
    rewrite h in E.
    rewrite E.
    unfold Even.
    exists k.
    reflexivity.
  - intros h.
    destruct h as [k E].
    rewrite E.
    apply even_double.
Qed.

(* Theorem eqb_eq: *)
(*   forall m n: nat, m =? n = true  <->  m = n. *)
(* Proof. *)
(*   intros m n. *)
(*   split. *)
(*   - apply Tactics.eqb_true. *)
(*   - intros h. *)
(*     rewrite h. *)
(*     apply Induction.eqb_refl. *)
(* Qed. *)
