
inductive Tower where
| A
| B
| C
deriving Repr, BEq, DecidableEq

structure Hanoi where
  src : Tower
  dest : Tower
  h : src ≠ dest
  n : Nat
deriving Repr

def aux (src dest : Tower) (h : src ≠ dest) : Tower :=
  match src, dest with
  | .A, .C => .B
  | .A, .B => .C
  | .B, .C => .A
  | .B, .A => .C
  | .C, .A => .B
  | .C, .B => .A
  | .A, .A => absurd rfl h
  | .B, .B => absurd rfl h
  | .C, .C => absurd rfl h

theorem aux_ne_src (src dest : Tower) (h : src ≠ dest) : aux src dest h ≠ src := by
  cases src <;> cases dest <;> (simp only [aux]; first | decide | contradiction)

theorem aux_ne_dest (src dest : Tower) (h : src ≠ dest) : aux src dest h ≠ dest := by
  cases src <;> cases dest <;> (simp only [aux]; first | decide | contradiction)

partial def solve (conf : Hanoi) : List (Tower × Tower) :=
  match conf.n with
  | 0 => []
  | n' + 1 =>
    let x := aux conf.src conf.dest conf.h
    solve { conf with dest := x, h := (aux_ne_src conf.src conf.dest conf.h).symm, n := n' }
    ++ [(conf.src, conf.dest)]
    ++ solve { conf with src := x, h := aux_ne_dest conf.src conf.dest conf.h, n := n' }

def hanoi (n : Nat) : Hanoi :=
  { src := .A, dest := .C, h := by decide, n := n }

#eval solve (hanoi 3)
