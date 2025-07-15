Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool: Type :=
  | true
  | false.

Definition negb (b: bool): bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (x: bool) (y: bool): bool :=
  match x with
  | true => y
  | false => false
  end.

Definition orb (x: bool) (y: bool): bool :=
  match x with
  | true => true
  | false => x
  end.

Example not_true_and_false:
  (andb (negb true) false) = false.
Proof. simpl. reflexivity. Qed.

Example true_or_false:
  orb true false = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).

Notation "x || y" := (orb x y).

Example or_notation:
  true || false = true.
Proof.  reflexivity. Qed.

Example and_notation:
  true && false = false.
Proof. reflexivity. Qed.

Definition negb' (b: bool): bool :=
  if b then false else true.

Example negs_are_equal:
  negb = negb'.
Proof. reflexivity. Qed.

Inductive black_white: Type :=
  | black
  | white.

Definition invert (x: black_white): black_white :=
  if x then white else black.

Example invert_white :
  invert white = black.
Proof. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool
  := negb (andb b1 b2).
Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb b1 (andb b2 b3).
Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check (negb true):bool.

Check negb: bool -> bool.

Inductive rgb: Type :=
  | red 
  | green
  | blue.

Inductive color: Type :=
  | bw (b: black_white)
  | primary (p: rgb).

Definition monochrome (c: color): bool :=
  match c with
  | bw _ => true
  | _ => false
  end.

Definition is_red (c: color): bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Example blue_is_not_red:
 (is_red (primary blue) = false).
Proof. simpl. reflexivity. Qed.

Module Playground.
  Definition foo: rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo: rgb.
Check foo:bool.

Module TuplePlayground.
  Inductive bit: Type :=
    | B₁
    | B₀.

  Inductive nybble: Type := 
  | bits (b₀ b₁ b₂ b₃ : bit).

  Check (bits B₀ B₁ B₀ B₁: nybble).

  Definition all_zero (nb: nybble) :=
    match nb with
    | bits B₀ B₀ B₀ B₀ => true
    | _ => false
    end.

  Example not_all_zero:
   all_zero (bits B₀ B₁ B₀ B₁) = false.
  Proof. reflexivity. Qed.
End TuplePlayground.
