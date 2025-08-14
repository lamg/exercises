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
