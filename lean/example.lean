#eval 1+3

#eval String.append "hello" " world"

def hello := "hello"

#eval hello

def add1 (x : Nat) : Nat := x + 1

#eval add1 10

structure Point where
  x : Nat
  y : Nat

#check ({ x := 10, y := 20 }:Point)

#check Nat -> Nat

