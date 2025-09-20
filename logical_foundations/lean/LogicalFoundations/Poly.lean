
theorem app_nil_r (t: Type) (xs: List t):
  xs ++ [] = xs
:= by
  induction xs with
  | nil => simp
  | cons x xs ih => simp

theorem app_assoc (t: Type) (xs ys zs: List t):
  xs ++ ys ++ zs = (xs ++ ys) ++ zs
:= by
  induction xs with
  | nil => simp
  | cons x xs ih => simp

theorem app_length (t: Type) (xs ys: List t):
  List.length (xs ++ ys) = List.length xs + List.length ys
:= by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp
    rw [Nat.add_assoc, Nat.add_comm ys.length, <- Nat.add_assoc]
