Require Export Rocq.Basics.

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

Definition not (p: Prop) := p -> False.

Notation "~ x" := (not x): type_scope.

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

Theorem nil_is_not_cons:
  forall t (x: t) (xs: list t),
    ~(nil = x :: xs).
Proof.
