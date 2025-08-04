From Rocq Require Import Induction.
From Rocq Require Import Basics.

Module NatList.
  Import NatPlayground.

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
        if odd x then x :: oddmembers xs else oddmembers xs
    end.

  Example test_oddmembers:
    oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. refl. Qed.

  Definition countoddmembers (xs: natlist) :=
    length (oddmembers xs).

  Example test_countoddmembers2:
    countoddmembers [0;2;4] = 0.
  Proof. refl. Qed.

  Example test_countoddmembers3:
    countoddmembers nil = 0.
  Proof. refl. Qed.

  Fixpoint alternate (l1 l2 : natlist) :=
    match l1, l2 with
      | nil, _ => l2
      | _, nil => l1
      | x :: xs, y :: ys => x :: y :: (alternate xs ys)
      end.


  Example test_alternate1:
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. refl. Qed.

  Example test_alternate2:
    alternate [1] [4;5;6] = [1;4;5;6].
  Proof. refl. Qed.

  Example test_alternate3:
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof. refl. Qed.

  Example test_alternate4:
    alternate [] [20;30] = [20;30].
  Proof. refl. Qed.

  Definition bag := natlist.

  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
      | nil => 0
      | x :: xs =>
          if eqb v x then S (count v xs) else count v xs
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. refl. Qed.

  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. refl. Qed.

  Definition sum := app.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. refl. Qed.

  Definition add (v : nat) (s : bag) : bag := v :: s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. refl. Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. refl. Qed.

  Fixpoint member (v : nat) (s : bag) : bool :=
    match s with
      | nil => false
      | x :: xs =>
          if eqb v x then true else member v xs
    end.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. refl. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. refl. Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
      | nil => nil
      | x :: xs =>
          if eqb x v then xs else x :: remove_one v xs
  end.

  Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. refl. Qed.

  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. refl. Qed.

  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. refl. Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. refl. Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
      | nil => nil
      | x :: xs =>
          if eqb x v then remove_all v xs else x :: remove_all v xs
    end.

  Example test_remove_all1:
    count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. refl. Qed.

  Example test_remove_all2:
    count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. refl. Qed.

  Example test_remove_all3:
    count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. refl. Qed.

  Example test_remove_all4:
    count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. refl. Qed.

  Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1 with
      | nil => true
      | x :: xs =>
          member x s2 && included xs (remove_one x s2)
  end.

  Example test_included1:
    included [1;2] [2;1;4;1] = true.
  Proof. refl. Qed.

  Example test_included2:
    included [1;2;2] [2;1;4;1] = false.
  Proof. refl. Qed.

  Lemma nat_identity:
    forall n, eqb n n = true.
  Proof.
    intro n.
    induction n as [|n' ind].
    - refl.
    - simpl. rewrite ind. refl.
  Qed.


  Theorem add_inc_count:
    forall (n:nat) (b:bag), count n (add n b) = S (count n b).
  Proof.
    intros n b.
    simpl.
    rewrite nat_identity.
    refl.
  Qed.


End NatList.
