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

Compute (next_working_day saturday).

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

Compute (andb (negb true) false).

