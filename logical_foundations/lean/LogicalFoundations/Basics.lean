inductive Day where
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday
deriving Repr, DecidableEq

open Day

def nextWorkingDay: Day -> Day
| monday => tuesday
| tuesday   => wednesday
| wednesday => thursday
| thursday  => friday
| friday    => monday
| saturday  => monday
| sunday    => monday

example: nextWorkingDay (nextWorkingDay saturday) = tuesday :=
by rfl

def negb (b: Bool) :=
  match b with
  | true => false
  | false => true

def andb (x y: Bool) :=
  match x,y with
  | true, true => true
  | _, _ => false

def orb (x y: Bool) :=
  match x, y with
  | false, false => false
  | _, _ => true

example: andb (negb true) false = false := by rfl

example: orb true false = true := by rfl

inductive black_white : Type where
| black
| white

inductive rgb: Type where
| red
| green
| blue

inductive color: Type where
| bw (b: black_white)
| primary (p: rgb)

def pred (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ n' => n'

def even (n: Nat): Bool :=
  match n with
  | 0 => true
  | Nat.succ (Nat.succ n) => even n
  | _ => false

def odd (n: Nat) := negb (even n)

def plus (n m : Nat): Nat :=
  match n with
  | 0 => m
  | Nat.succ n' => Nat.succ (plus n' m)

def mult (n m : Nat): Nat :=
  match n with
  | 0 => 0
  | Nat.succ n' => plus m (mult n' m)

def minus (n m : Nat) :=
  match n, m with
  | 0, _ => 0
  | _, 0 => n
  | Nat.succ n', Nat.succ m' => minus n' m'

def exp (base power: Nat) :=
  match power with
  | 0 => 1
  | Nat.succ p => mult base (exp base p)

def factorial (n: Nat) :=
  match n with
  | 0 => 1
  | Nat.succ n' => mult n (factorial n')

def eqb (n m : Nat) :=
  match n, m with
  | 0, 0 => true
  | Nat.succ n', Nat.succ m' => eqb n' m'
  | _, _ => false

def leb (n m : Nat) :=
  match n, m with
  | 0, _ => true
  | Nat.succ n', Nat.succ m' => leb n' m'
  | _, _ => false

def gt (n m : Nat) :=
  match n, m with
  | Nat.succ _, 0 => true
  | Nat.succ n', Nat.succ m' => gt n' m'
  | _, _ => false

theorem plus_0_n (n: Nat): 0 + n = n := by simp

theorem mult_0_n (n: Nat): 0 * n = 0 := by simp

theorem plus_id_example (n m : Nat):
  n = m -> n + n = m + m
:= by
  intros h
  rewrite [h]
  rfl

theorem plus_id_exercise (n m p: Nat):
  n = m -> m = p -> n + m = m + p
:= by
  intros h0 h1
  rewrite [h0, h1]
  rfl

theorem mult_n_0 (n: Nat):
  n * 0 = 0
:= by
  simp

theorem mult_n_0_m_0 (n m: Nat):
  n * 0 + m * 0 = 0
:= by
  rewrite [mult_n_0, mult_n_0]
  rfl

theorem mult_n_succ_m (n m : Nat):
  n * m + n = n * Nat.succ m
:= by
  rfl

theorem mult_p_one (p : Nat) :
  p * 1 = p
:= by
  rewrite [<- mult_n_succ_m]
  rewrite [mult_n_0]
  simp

theorem plus_1_neq_0 (n: Nat):
  ((n + 1) == 0) = false
:= by
  cases n with
  | zero => rfl
  | succ n' => rfl

theorem negb_is_involutive (b: Bool):
  negb (negb b) = b
:= by
  cases b with
  | false => rfl
  | true => rfl

theorem andb_is_commutative(x y : Bool):
  (x && y) = (y && x)
:= by
  cases x with
  | false =>
    cases y with
    | false => rfl
    | true => rfl
  | true =>
    cases y with
    | false => rfl
    | true => rfl

theorem andb3_exchange(x y z: Bool):
  ((x && y) && z) = (x && (y && z))
:= by
  cases x <;> cases y <;> cases z <;> rfl

theorem andb_true_elim2(x y : Bool):
  (x && y) = true -> (y = true)
:= by
  cases x <;> cases y <;> simp

theorem plus_one_neq_0'(n: Nat):
  (n + 1 == 0) = false
:= by
  cases n <;> simp

theorem identity_fn_applied_twice (f: Bool -> Bool) (h: ∀ x, f x = x):
  ∀ b, f (f b) = b
:= by
  intro b
  rewrite [h, h]
  rfl

theorem negation_fn_applied_twice
  (f: Bool -> Bool)
  (h: ∀ x, f x = negb x)
  (b: Bool):
  f (f b) = b
:= by
  rewrite [h,h]
  rewrite [negb_is_involutive]
  rfl

theorem andb_eq_orb (x y: Bool):
 (x && y) = (x || y) ->  x = y
:= by
  cases x <;> simp

inductive letter where | A | B | C | D | F

inductive modifier where | Plus | Natural | Minus

inductive grade where | Grade (l: letter) (m: modifier)

inductive comparison where | Eq | Lt | Gt

open letter
open modifier
open grade
open comparison

def letter_comparison (l0 l1: letter) :=
  match l0, l1 with
  | A, A => comparison.Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, A
  | C, B => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, A
  | D, B
  | D, C => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, A
  | F, B
  | F, C
  | F, D => Lt
  | F, F => Eq

theorem letter_comparison_eq (l: letter):
  letter_comparison l l = comparison.Eq
:= by
  cases l <;> rfl

def modifier_comparison (m₀ m₁: modifier) :=
  match m₀, m₁ with
  | Plus, Plus => comparison.Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, Plus
  | Minus, Natural => Lt
  | Minus, Minus => Eq

def grade_comparison (g₀ g₁: grade) :=
  match g₀, g₁ with
  | grade.Grade l₀ m₀, grade.Grade l₁ m₁ =>
    match letter_comparison l₀ l₁ with
    | comparison.Eq => modifier_comparison m₀ m₁
    | r => r

example: grade_comparison (Grade A Minus) (Grade B Plus) = Gt := by rfl

example: grade_comparison (Grade A Minus) (Grade A Plus) = Lt := by rfl

example: grade_comparison (Grade F Plus) (Grade F Plus) = comparison.Eq := by rfl

example: grade_comparison (Grade B Minus) (Grade C Plus) = Gt := by rfl

def lower_letter (l: letter) :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F

theorem lower_letter_lowers (l: letter):
  letter_comparison F l = Lt ->
  letter_comparison (lower_letter l) l = Lt
:= by
  intro h
  cases l with
  | F => rewrite [<-h]; rfl
  | _ => rfl

def lower_grade (g: grade) :=
  match g with
  | Grade F Minus => Grade F Minus
  | Grade l Minus => Grade (lower_letter l) Plus
  | Grade l Plus => Grade l Natural
  | Grade l Natural => Grade l Minus

theorem lower_grade_lowers (g: grade):
  grade_comparison (Grade F Minus) g = Lt ->
  grade_comparison (lower_grade g) g = Lt
:= by
  intros h
  cases g with
  | Grade l m =>
    cases l <;> cases m <;>
      first
      | rewrite [←h]; rfl  -- succeeds only when l = F, m = Minus
      | rfl                  -- succeeds in all the other cases

def apply_late_policy (late_days: Nat) (g: grade) :=
  if Nat.blt late_days 9 then g
  else if Nat.blt late_days 17 then lower_grade g
  else if Nat.blt late_days 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g))

theorem no_penalty_for_mostly_on_time (late_days:Nat) (g: grade):
  Nat.blt late_days 9 = true -> apply_late_policy late_days g = g
:= by
  intro h
  unfold apply_late_policy
  rewrite [h]
  simp

theorem grade_lowered_once (late_days: Nat) (g: grade):
    Nat.blt late_days 9 = false ->
    Nat.blt late_days 17 ->
    apply_late_policy late_days g = lower_grade g
:= by
  intros not_9 lt_17
  unfold apply_late_policy
  rewrite [not_9, lt_17]
  simp

inductive bin where
  | Z
  | B₀ (n: bin)
  | B₁ (n: bin)

open bin

def incr (m: bin) :=
  match m with
  | B₀ b => B₁ b
  | B₁ b => B₀ (incr b)
  | Z => B₁ Z

def bin_to_nat (m: bin) :=
  match m with
  | Z => 0
  | B₀ b => 2 * bin_to_nat b
  | B₁ b => 1 + (2 * bin_to_nat b)

example: incr (B₁ Z) = B₀ (B₁ Z) := by rfl

example: incr (B₀ (B₁ Z)) = B₁ (B₁ Z) := by rfl

example: incr (B₁ (B₁ Z)) = B₀ (B₀ (B₁ Z)) := by rfl

example: bin_to_nat (B₀ (B₁ Z)) = 2 := by rfl

example: bin_to_nat (incr (B₁ Z)) = 1 + bin_to_nat (B₁ Z) := by rfl

example: bin_to_nat (incr (incr (B₁ Z))) = 2 + bin_to_nat (B₁ Z) := by rfl
