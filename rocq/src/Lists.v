From Rocq Require Import Induction.
From Rocq Require Import Basics.

Module NatList.

  Inductive natprod: Type :=
    | pair (n0 n1 : nat).

  Check (pair 3 5) : natprod.

  Definition fst (p : natprod) :=
    match p with
      | pair x _ => x
    end.

  Definition snd (p : natprod) :=
    match p with
      | pair _ y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition swap_pair (p: natprod) :=
    match p with
      | (x,y) => (y,x)
    end.

  Theorem swap_pair_involutive:
    forall x y:nat, swap_pair (swap_pair (x,y)) = (x,y).
    Proof.
      refl.
    Qed.

  Theorem surjective_pairing':
    forall n m:nat,
      (n,m) = (fst (n,m), snd (n,m)).
    Proof.
      refl.
    Qed.

  Theorem surjective_pairing_stuck:
    forall p: natprod,
      p = (fst p, snd p).
    Proof. simpl. Abort.

  Theorem surjective_pairing:
    forall p: natprod,
      p = (fst p, snd p).
    Proof.
      intro p.
      destruct p as [n m].
      refl.
    Qed.

  Theorem snd_fst_is_swap:
    forall p: natprod,
      (snd p, fst p) = swap_pair p.
    Proof.
      intro p.
      destruct p as [n m].
      refl.
    Qed.

  Theorem fst_swap_is_snd:
    forall p, fst (swap_pair p) = snd p.
  Proof.
    intro p.
    destruct p as [n m].
    refl.
  Qed.

  Inductive natlist: Type :=
    | nil
    | cons (n : nat) (ns: natlist).

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[  ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) :=
    match count with
    | 0 => nil
    | S count' => n :: (repeat n count')
    end.

  Fixpoint length (xs: natlist) :=
    match xs with
      | nil => 0
      | y :: ys => S (length ys)
    end.

  Fixpoint app (xs ys : natlist) :=
    match xs with
      | nil => ys
      | z :: zs => z :: (app zs ys) end.

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Example test_app0:
    [1;2;3] ++ [4; 5] = [1;2;3;4;5].
  Proof. refl. Qed.

  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. refl. Qed.
  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. refl. Qed.
  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. refl. Qed.

  Definition hd (default: nat) (xs: natlist) :=
    match xs with
      | nil => default
      | x :: _ => x
    end.

  Definition tl (xs: natlist) :=
    match xs with
      | nil => nil
      | _ :: ys => ys
    end.

  Example test_hd1: hd 0 [1;2;3] = 1.
  Proof. refl. Qed.

  Example test_hd2: hd 0 [] = 0.
  Proof. refl. Qed.

  Example test_tl: tl [1;2;3] = [2;3].
  Proof. refl. Qed.

  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
      | nil => nil
      | 0 :: xs => nonzeros xs
      | x :: xs => x :: nonzeros xs
    end.

  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. refl. Qed.

  Fixpoint oddmembers (l:natlist) :=
    match l with
    | nil => nil
    | x :: xs =>
        if NatPlayground.odd x then x :: oddmembers xs else oddmembers xs
    end.
  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. refl. Qed.


End NatList.
