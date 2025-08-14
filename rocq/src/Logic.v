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
  induction n as [|n' ind].
  - simpl in eq.
    split.
    + reflexivity.
    + apply eq.
  - split.
    + discriminate eq.
    + discriminate eq.
Qed.
