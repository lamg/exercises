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
Proof reflexivity.
Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Admitted.