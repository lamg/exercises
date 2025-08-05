From Rocq Require Export Lists.

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

  Check (d mumble (b a 5)).
  Check (d bool (b a 5)).
  Check (e bool true).
  Check (e mumble (b c 0)).
  Check c.

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


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
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

Check @nil : forall X : Type, list X.

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
