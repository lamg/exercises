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
      | [] => default
      | x :: _ => x
    end.

  Definition tl (xs: natlist) :=
    match xs with
      | [] => []
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
      | [] => []
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
    countoddmembers [] = 0.
  Proof. refl. Qed.

  Fixpoint alternate (l1 l2 : natlist) :=
    match l1, l2 with
      | [], _ => l2
      | _, [] => l1
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
      | [] => 0
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
      | [] => false
      | x :: xs =>
          if eqb v x then true else member v xs
    end.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. refl. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. refl. Qed.

  Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
      | [] => []
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
      | [] => []
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
      | [] => true
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

 Theorem nil_app :
   forall l : natlist, [] ++ l = l.
 Proof. refl. Qed.

 Theorem tl_length_pred :
   forall l:natlist,
   pred (length l) = length (tl l).
 Proof.
  intros l.
  destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.
 Qed.

 Theorem app_assoc:
   forall l0 l1 l2: natlist,
     (l0 ++ l1) ++ l2 = l0 ++ (l1 ++ l2).
   Proof.
     intros l0 l1 l2.
     induction l0 as [|n l0 ind].
     - refl.
     - simpl. rewrite ind. refl.
  Qed.

 Theorem repeat_double_firsttry :
   forall c n: nat,
     repeat n c ++ repeat n c = repeat n (c + c).
 Proof.
   intro c.
   induction c as [|c' indC].
   - intro n. simpl. refl.
   - intro n. simpl.
 Abort.

 Theorem repeat_plus:
   forall c0 c1 n: nat,
     repeat n c0 ++ repeat n c1 = repeat n (c0 + c1).
   Proof.
     intros c0 c1 n.
     induction c0 as [|c0' ind].
     - simpl. refl.
     - simpl. rewrite ind. refl.
  Qed.

  Fixpoint rev (l: natlist) :=
    match l with
      | [] => []
      | h :: t => rev t ++ [h]
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem rev_length_firsttry:
    forall l, length (rev l) = length l.
  Proof.
    intro l.
    induction l as [|n l' ind].
    - simpl. refl.
    - simpl.
  Abort.

  Theorem app_rev_length_S_firsttry:
    forall l n,
      length (rev l ++ [n]) = S (length (rev l)).
  Proof.
    intro l.
    induction l as [| m l' ind].
    - intro n. simpl. refl.
    - intro n. simpl.
  Abort.

  Theorem app_length_S:
    forall l n, length (l ++ [n]) = S (length l).
  Proof.
    intro l.
    induction l as [| m l' ind].
    - refl.
    - intro n. simpl. rewrite ind. refl.
  Qed.

  Theorem rev_length:
    forall l, length (rev l) = length l.
  Proof.
    intro l.
    induction l as [|n l' ind].
    - simpl. refl.
    - simpl. rewrite <- ind. rewrite app_length_S. refl.
  Qed.

  Theorem app_length:
    forall l0 l1, length (l0 ++ l1) = length l0 + length l1.
  Proof.
    intros l0 l1.
    induction l0 as [|n l' ind].
    - simpl. refl.
    - simpl. rewrite ind. refl.
  Qed.

  Theorem app_nil_r:
    forall l: natlist, l ++ [] = l.
  Proof.
    intro l.
    induction l as [|n l' ind].
    - refl.
    - simpl. rewrite ind. refl.
  Qed.

  Theorem rev_app_distr:
    forall l0 l1, rev (l0 ++ l1) = rev l1 ++ rev l0.
  Proof.
    intros l0 l1.
    induction l0 as [|n l' ind].
    - simpl. rewrite app_nil_r. refl.
    - simpl. rewrite ind. rewrite app_assoc. refl.
  Qed.

  Theorem rev_involutive:
    forall l, rev (rev l) = l.
  Proof.
    intro l.
    induction l as [|n l' ind].
    - refl.
    - simpl. rewrite rev_app_distr. rewrite ind. simpl. refl.
  Qed.

  Theorem app_assoc4:
    forall l0 l1 l2 l3, l0 ++ (l1 ++ (l2 ++ l3)) = ((l0 ++ l1) ++ l2) ++ l3.
  Proof.
    intros l0 l1 l2 l3.
    rewrite app_assoc.
    rewrite app_assoc.
    refl.
  Qed.

  Lemma nonzeros_app:
    forall l0 l1, nonzeros (l0 ++ l1) = nonzeros l0 ++ nonzeros l1.
  Proof.
    intros l0 l1.
    induction l0 as [|n l0' ind].
    - refl.
    - simpl.
      destruct n eqn:E.
      + rewrite ind. refl.
      + simpl. rewrite ind. refl.
    Qed.

  Fixpoint eqblist (l0 l1: natlist) :=
    match l0, l1 with
      | [], [] => true
      | x :: xs, y :: ys =>
          eqb x y && eqblist xs ys
      | _, _ => false
    end.

  Example test_eqblist1 : (eqblist nil nil = true). Proof. refl. Qed.
  Example test_eqblist2 :eqblist [1;2;3] [1;2;3] = true. Proof. refl. Qed.
  Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false. Proof. refl. Qed.

  Theorem eqblist_refl :
    forall l:natlist, true = eqblist l l.
  Proof.
    intro l.
    induction l as [|n l' ind].
    - refl.
    - simpl. rewrite nat_identity. simpl. rewrite ind. refl.
  Qed.

  Theorem count_member_nonzero:
    forall s, leb 1 (count 1 (1 :: s)) = true.
  Proof.
    intro s.
    simpl.
    refl.
  Qed.

  Theorem leb_n_Sn:
    forall n, leb n (S n) = true.
  Proof.
    intro n.
    induction n as [|n' ind].
    - refl.
    - simpl. rewrite ind. refl.
  Qed.

  Theorem remove_does_not_increase_count:
    forall s, leb (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intro s.
    induction s as [|n s' ind].
    - refl.
    - simpl.
      destruct n eqn:E.
      + simpl. rewrite leb_n_Sn. refl.
      + simpl. rewrite ind. refl.
  Qed.

  Theorem bag_count_sum:
    forall n s0 s1, count n (s0 ++ s1) = count n s0 + count n s1.
  Proof.
    intros n s0 s1.
    induction s0 as [|m s0' ind].
    - simpl. refl.
    - simpl.
      destruct (eqb n m) eqn:E.
      + simpl. rewrite ind. refl.
      + rewrite ind. refl.
  Qed.

  Theorem involution_injective:
    forall (f: nat -> nat),
      (forall n, f (f n) = n) -> (forall p q, f p = f q -> p = q).
  Proof.
    intro f.
    intro involutive.
    intros p q.
    intro equal_image.
    rewrite <- involutive.
    rewrite <- equal_image.
    rewrite involutive.
    refl.
  Qed.

  Theorem rev_injective:
    forall l0 l1, rev l0 = rev l1 -> l0 = l1.
  Proof.
    intros l0 l1.
    intro p.
    rewrite <- rev_involutive.
    rewrite <- p.
    rewrite rev_involutive.
    refl.
  Qed.

End NatList.


Module NatOption.
  Import NatList.

  Inductive natoption: Type :=
    | Some (n: nat)
    | None.

  Fixpoint nth_error (xs: natlist) (n:nat) :=
    match xs with
      | [] => None
      | x :: xs =>
          match n with
          | 0 => Some x
          | S n' => nth_error xs n'
          end
    end.

  Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
  Proof. reflexivity. Qed.
  Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
  Proof. reflexivity. Qed.
  Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d : nat) (o : natoption) : nat :=
    match o with
    | Some n' => n'
    | None => d
  end.

  Definition hd_error (l: natlist) :=
    match l with
      | [] => None
      | x :: _ => Some x
    end.

  Example test_hd_error1 : hd_error [] = None.
  Proof. reflexivity. Qed.
  Example test_hd_error2 : hd_error [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_error3 : hd_error [5;6] = Some 5.
  Proof. reflexivity. Qed.


  Theorem option_elim_hd :
    forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_error l).
  Proof.
    intros l n.
    destruct l eqn:E.
    - simpl. refl.
    - simpl. refl.
  Qed.
End NatOption.


Module PartialMap.
  Import NatPlayground.
  Import NatList.
  Import NatOption.

  Inductive id: Type :=
    | Id (n: nat).

  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => eqb n1 n2
  end.

  Inductive partial_map: Type :=
    | empty
    | record (i : id) (v : nat) (m : partial_map).

  Definition update (d : partial_map) (x : id) (value : nat):=
    record x value d.

  Fixpoint find (x : id) (d : partial_map) : natoption :=
    match d with
    | empty => None
    | record y v d' =>
        if eqb_id x y then Some v else find x d'
  end.

  Theorem update_eq :
    forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
  Proof.
    intros d x v.
    simpl.
    destruct x eqn:E.
    simpl.
    rewrite nat_identity.
    refl.
  Qed.

  Theorem update_neq :
    forall (d : partial_map) (x y : id) (n: nat),
      eqb_id x y = false -> find x (update d y n) = find x d.
  Proof.
    intros d x y n.
    intro cond.
    simpl.
    rewrite cond.
    refl.
  Qed.
End PartialMap.
