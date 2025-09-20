import LogicalFoundations.Basics

theorem add_0_right (n: Nat):
  n + 0 = n
:= by
  induction n with
  | zero => rfl
  | succ n ih => simp

theorem minus_n_n (n: Nat):
  n - n = 0
:= by
  simp

theorem mul_0_right (n: Nat):
  n * 0 = 0
:= by
  simp

theorem plus_n_S_m (n m : Nat):
  Nat.succ (n + m) = n + (Nat.succ m)
:= by
  induction n with
  | zero => rfl
  | succ k ih => rfl

theorem add_commutativity (n m : Nat):
  n + m = m + n
:= by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [Nat.succ_add]
    rw [<- (plus_n_S_m m k)]
    rw [<- ih]

theorem add_assoc (n m p: Nat):
  n + (m + p) = (n + m) + p
:= by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [Nat.succ_add]
    rw [ih]

def double (n: Nat) :=
  match n with
  | 0 => 0
  | Nat.succ n' => Nat.succ (Nat.succ (double n'))

theorem double_plus (n : Nat):
  double n = n + n
:= by
  induction n with
  | zero => simp [double]
  | succ k ih =>
    simp [double]
    rw [ih]
    rw [ <- plus_n_S_m (k + 1) k]
    rw [add_commutativity (k + 1) k ]
    rw [<- plus_n_S_m k k]

theorem eqb_rfl (n : Nat):
  eqb n n = true
:= by
  induction n with
  | zero => simp [eqb]
  | succ k ih =>
    simp [eqb]
    apply ih

theorem even_succ (n : Nat):
  even (n + 1) = negb (even n)
:= by
  induction n with
  | zero => simp [even, negb]
  | succ n ih =>
    rw [ih]
    rw [negb_is_involutive]
    simp [even]

theorem mult_0_plus' (m n : Nat):
  (n + 0 + 0) * m = n * m
:= by
  have H: n + 0 + 0 = n := by simp
  rw [H]

theorem plus_rearrange(n m p q: Nat):
  (n + m) + (p + q) = (m + n) + (p + q)
:= by
  have H: n + m = m + n := by apply add_commutativity
  rw [H]

theorem add_shuffle3 (n m p : Nat):
  n + (m + p) = m + (n + p)
:= by
  rw [add_assoc]
  have H: n + m = m + n := by apply add_commutativity
  rw [H]
  rw [add_assoc]

theorem mult_n_S_m (n m : Nat):
  n * m + n = n * (m + 1)
:= by
  induction n with
  | zero => simp
  | succ n ih => rfl

theorem mult_commutativity (n m : Nat):
  m * n = n * m
:= by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [<- mult_n_S_m ]
    simp [Nat.succ_mul]
    rw [ih]

theorem pluss_leb_compat_l (n m p : Nat):
  n <=? m = true -> (p + n) <=? (p + m) = true
:= by
  induction p with
  | zero => simp
  | succ p ih =>
    intros H
    simp [Nat.succ_add, leb]
    apply ih
    apply H

theorem leb_refl (n : Nat):
  n <=? n = true
:= by
  induction n with
  | zero => simp [leb]
  | succ n ih =>
    simp [leb]
    apply ih

theorem zero_neqb_S (n : Nat):
  0 =? n + 1 = false
:= by
  rfl

theorem mult_1_l (n: Nat):
  1 * n = n
:= by
  simp

theorem all3_spec (a b : Bool):
  orb (andb a b) (orb (negb a) (negb b)) = true
:= by
  cases a with
  | true =>
    cases b with
    | true => simp [negb, orb, andb]
    | false => simp [negb, orb, andb]
  | false => simp [andb, negb, orb]

theorem mult_plus_distr_r (n m p : Nat):
  (n + m) * p = (n * p) + (m * p)
:= by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [ <- mult_n_S_m, <- mult_n_S_m, <- mult_n_S_m ]
    rw [ih]
    have H: n + (m * p + m) = m * p + (n + m) := by
      rw [add_shuffle3]
    rw [ <-add_assoc, <-add_assoc]
    rw [H]

theorem mult_assoc (n m p: Nat):
  n * (m * p) = (n * m) * p
:= by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [mult_plus_distr_r]
    simp
    rw [mult_plus_distr_r]
    simp
    rw [mult_plus_distr_r]
    rw [ih]

inductive my_bin: Type where
| Z
| B₀ (n: my_bin)
| B₁ (n: my_bin)
open my_bin

def incr_my_bin (m: my_bin) :=
  match m with
  | .Z => B₁ Z
  | .B₀ b => B₁ b
  | .B₁ b => B₀ (incr_my_bin b)

def my_bin_to_nat (m: my_bin): Nat :=
  match m with
  | .Z => 0
  | .B₀ b => double (my_bin_to_nat b)
  | .B₁ b => double (my_bin_to_nat b) + 1

theorem bit_to_nat_pres_incr (b : my_bin):
  my_bin_to_nat (incr_my_bin b) = my_bin_to_nat b + 1
:= by
  induction b with
  | Z =>
    simp [incr_my_bin, my_bin_to_nat]
    rfl
  | B₀ n ih =>
    simp [incr_my_bin, my_bin_to_nat]
  | B₁ n ih =>
    simp [incr_my_bin, my_bin_to_nat]
    rw [ih]
    simp [double]


def nat_to_my_bin (n: Nat): my_bin :=
  match n with
  | 0 => Z
  | .succ n => incr_my_bin (nat_to_my_bin n)

theorem double_incr (n: Nat):
  (double n.succ) = (double n).succ.succ
:= by
  simp [double]

def double_bin (b: my_bin) :=
  match b with
  | Z => Z
  | _ => B₀ b
