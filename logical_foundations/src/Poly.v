From LogicalFoundations Require Export Basics.
From LogicalFoundations Require Export Lists.
Require Export Stdlib.Init.Nat.

Inductive list (T: Type) : Type :=
  | nil
  | cons (x : T) (xs: list T).

Fixpoint repeat (T : Type) (x : T) (count : nat) : list T :=
  match count with
  | 0 => nil T
  | S count' => cons T x (repeat T x count')
end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
  Inductive mumble : Type :=
    | a
    | b (x : mumble) (y : nat)
    | c.

  Inductive grumble (T:Type) : Type :=
    | d (m : mumble)
    | e (x : T).

  (* Check (d mumble (b a 5)). *)
  (* Check (d bool (b a 5)). *)
  (* Check (e bool true). *)
  (* Check (e mumble (b c 0)). *)
  (* C heck c. *)

End MumbleGrumble.

Fixpoint repeat' T x count : list T :=
  match count with
  | 0 => nil T
  | S count' => cons T x (repeat' T x count')
end.

Fixpoint repeat'' T x count : list T :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
end.

Arguments nil {T}.
Arguments cons {T}.
Arguments repeat {T}.

Fixpoint repeat''' {T: Type} (x:T) (count:nat) : list T :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
end.


Fixpoint app {t : Type} (l1 l2 : list t) : list t :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {t:Type} (l:list t) : list t :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {t : Type} (l : list t) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Definition list123''' := [1; 2; 3].

Theorem app_nil_r:
  forall (t: Type), forall l: list t,
    l ++ [] = l.
Proof.
  intros t l.
  induction l as [|x l' ind].
  - reflexivity.
  - simpl. rewrite ind. reflexivity.
Qed.

Theorem app_assoc:
  forall t (l m n: list t),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros t l m n.
  induction l as [|x l' ind].
  - reflexivity.
  - simpl. rewrite ind. reflexivity.
Qed.

Lemma app_length:
  forall (t: Type) (l0 l1: list t),
    length (l0 ++ l1) = length l0 + length l1.
Proof.
  intros t l0 l1.
  induction l0 as [|x l0' ind].
  - reflexivity.
  - simpl. rewrite ind. reflexivity.
Qed.

Theorem rev_app_distr:
  forall t (l0 l1: list t),
    rev (l0 ++ l1) = rev l1 ++ rev l0.
Proof.
  intros t l0 l1.
  induction l0 as [|x l0' ind].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite ind. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive:
  forall (t:Type) (l: list t), rev (rev l) = l.
Proof.
  intros t l.
  induction l as [|n l' ind].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite ind. simpl. reflexivity.
Qed.

Theorem rev_injective:
  forall (t: Type) (l0 l1: list t), rev l0 = rev l1 -> l0 = l1.
Proof.
  intros t l0 l1.
  intro p.
  rewrite <- rev_involutive.
  rewrite <- p.
  rewrite rev_involutive.
  reflexivity.
Qed.

Inductive prod (t u: Type): Type :=
  | pair (x : t) (y: u).
Arguments pair {t} {u}.
Notation "( x , y )" := (pair x y).

Definition fst {t u: Type} (p: prod t u) :=
  match p with
  | (x, _) => x
end.

Definition snd {t u: Type} (p: prod t u) :=
  match p with
  | (_, y) => y
end.

Fixpoint combine {t u : Type} (l0 : list t) (l1 : list u) :=
  match l0, l1 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: (combine xs ys)
end.

(* Check @combine. *)

Example test_combine:
  combine [1;2] [false;true;false] = [(1,false);(2,true)].
Proof. reflexivity. Qed.

Fixpoint split {t u : Type} (l : list (prod t u)) : prod (list t) (list u) :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' =>
      match split l' with
      | (xs, ys) => (x :: xs, y :: ys)
      end
end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.
  Inductive option (t: Type): Type :=
    | Some (x:t)
    | None.
  Arguments Some {t}.
  Arguments None {t}.
End OptionPlayground.

Import OptionPlayground.

Fixpoint nth_error {t: Type} (l: list t) (n: nat): option t :=
  match l with
    | nil => None
    | x :: xs =>
        match n with
        | 0 => Some x
        | S n' => nth_error xs n'
        end
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {t: Type} (l: list t): option t :=
  match l with
    | nil => None
    | x :: _ => Some x
end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {t : Type} (f : t -> t) (n : t) : t :=
  f (f (f n)).

Import NatPlayground.

Example test_doit3times: doit3times minus2 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {t: Type} (test: t -> bool) (xs: list t) : list t :=
  match xs with
  | [] => []
  | x :: xs =>
    if test x then x :: (filter test xs) else filter test xs
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {t : Type} (l : list t) : bool := (length l) =? 1.

Example test_filter2:
  filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_non_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (xs: list nat) :=
  filter (fun x => gt x 7 && even x) xs.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {t: Type} (f: t -> bool) (xs: list t): prod (list t) (list t) :=
  (filter (fun x => f x) xs, filter (fun x => negb (f x)) xs).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {t u: Type} (f: t -> u) (xs : list t): list u :=
  match xs with
  | [] => []
  | x :: xs => (f x) :: (map f xs)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
  map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_app:
  forall (t u: Type) (f: t -> u) (xs ys: list t),
  map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  intros t u f xs ys.
  induction xs as [|x xs' ind].
  - simpl. reflexivity.
  - simpl. rewrite ind. reflexivity.
Qed.

Theorem map_rev:
  forall (t u: Type) (f: t -> u) (xs: list t),
    map f (rev xs) = rev (map f xs).
Proof.
  intros t u f xs.
  induction xs as [|x xs' ind].
  - simpl. reflexivity.
  - simpl. rewrite map_app. rewrite ind. reflexivity.
Qed.

Fixpoint flat_map {t u: Type} (f: t -> list u) (xs: list t): list u :=
  match xs with
  | [] => []
  | x :: xs => f x ++ flat_map f xs
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {t u: Type} (f : t -> u) (x : option t) : option u :=
  match x with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {t u: Type} (f: t -> u -> u) (xs: list t) (acc: u): u :=
  match xs with
  | [] => acc
  | x :: xs => f x (fold f xs acc)
end.

Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Example fold_diff_types:
  fold cons [] [1; 2; 3] = [1;2;3].
Proof. reflexivity. Qed.

Definition constfun {t: Type} (x: t) : nat -> t := fun (k:nat) => x.
Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct :
  forall t (l : list t), fold_length l = length l.
Proof.
  intros t l.
  induction l as [|x l' ind].
  - reflexivity.
  - simpl. rewrite <- ind. reflexivity.
Qed.

Definition fold_map {t u: Type} (f: t -> u) (xs: list t) : list u :=
  fold (fun x acc => f x :: acc) xs [].

Theorem fold_map_correct:
  forall (t u: Type) (xs: list t) (f: t -> u),
    fold_map f xs = map f xs.
Proof.
  intros t u xs f.
  induction xs as [|x xs' ind].
  - reflexivity.
  - simpl. rewrite <- ind. reflexivity.
Qed.

Definition prod_curry {t u v : Type}
  (f : prod t u -> v) (x : t) (y : u) : v := f (x, y).

Definition prod_uncurry {t u v : Type}
  (f : t -> u -> v) (p : prod t u) : v := (f (fst p)) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem uncurry_curry:
  forall (t u v: Type) (f: t -> u -> v) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros t u v f x y.
  reflexivity.
Qed.

Theorem curry_uncurry:
  forall (t u v: Type) (f: prod t u -> v) (p: prod t u),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros t u v f p.
  destruct p eqn:E.
  reflexivity.
Qed.

Theorem nth_error_index_out_of_range:
  forall t xs n,
    length xs = n -> @nth_error t xs n = None.
Proof.
  intros t xs n.
  intro cond.
Abort.

Module Church.
  Definition cnat := forall t: Type, (t -> t) -> t -> t.
  Definition zero: cnat := fun (t: Type) (_: t -> t) (zero: t) => zero.
  Definition one: cnat := fun (t: Type) (succ: t -> t) (zero: t) => succ zero.
  Definition two: cnat := fun (t: Type) (succ: t -> t) (zero: t) => succ (succ zero).
  Definition three: cnat := @doit3times.

  Example zero_church_peano:
    zero nat S O = 0.
  Proof. reflexivity. Qed.

  Example one_church_peano:
    one nat S O = 1.
  Proof. reflexivity. Qed.

  Example two_church_peano:
    two nat S O = 2.
  Proof. reflexivity. Qed.

  Definition scc (n: cnat): cnat :=
    fun (t: Type) (succ: t -> t) (zero: t) => succ (n t succ zero).

  Example scc_1 : scc zero = one.
  Proof. reflexivity. Qed.
  Example scc_2 : scc one = two.
  Proof. reflexivity. Qed.
  Example scc_3 : scc two = three.
  Proof. reflexivity. Qed.

  Definition plus (n m: cnat): cnat :=
    fun (t: Type) (succ: t -> t) (zero: t) => m t succ (n t succ zero).

  Example plus_1 : plus zero one = one.
  Proof. reflexivity. Qed.
  Example plus_2 : plus two three = plus three two.
  Proof. reflexivity. Qed.
  Example plus_3 :
    plus (plus two two) three = plus one (plus three three).
  Proof. reflexivity. Qed.

  Definition mult (n m : cnat): cnat :=
    fun (t: Type) (succ: t -> t) (zero: t) =>
      m t (n t succ) zero.

  Example mult_1 : mult one one = one.
  Proof. reflexivity. Qed.

  Example mult_2 : mult zero (plus three three) = zero.
  Proof. reflexivity. Qed.
  Example mult_3 : mult two three = plus three three.
  Proof. reflexivity. Qed.

  Definition conv (t:Type) (x: t) := fun (_:Type) (_: t -> t) (_:t) => t.

  Definition exp (n m: cnat) : cnat :=
    fun (t: Type) (succ: t -> t) (zero: t) =>
      m (t -> t) (n t) succ zero.

  Definition four := scc three.

  Example two_squared:
    exp two two nat S O = 4.
  Proof. reflexivity. Qed.

  Example three_cubed:
    exp three three nat S O = 27.
  Proof. reflexivity. Qed.

  Example four_cubed:
    exp four three nat S O = 64.
  Proof. reflexivity. Qed.

  Example four_zero:
    exp four zero nat S O = 1.
  Proof. reflexivity. Qed.

  Example three_four:
    exp three four nat S O = 81.
  Proof. reflexivity. Qed.

  Example exp_2 : exp three zero = one.
  Proof. reflexivity. Qed.

  Example exp_1 : exp two two = four.
  Proof. reflexivity. Qed.

  Example exp_3 : exp three two = plus (mult two (mult two two)) one.
  Proof. reflexivity. Qed.

End Church.
