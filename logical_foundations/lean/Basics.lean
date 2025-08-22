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
