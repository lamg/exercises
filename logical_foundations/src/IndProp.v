Require Export Logic.
Require Export Basics.
Require Export Poly.
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
