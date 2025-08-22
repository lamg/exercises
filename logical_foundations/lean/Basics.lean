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
  andb x y == andb y x
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
