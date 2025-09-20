def injective {t u} (f : t -> u): Prop :=
  ∀ x y: t, f x = f y -> x = y

theorem succ_inj:
  injective Nat.succ
:= by
  unfold injective
  intros x y H
  injection H

example:
  3 + 4 = 7 ∧ 2 * 2 = 4
:= by
  constructor
  . rfl
  . rfl

theorem plus_is_0 (n m : Nat):
  n + m = 0 -> n = 0 ∧ m = 0
:= by
  intros H
  cases n with
  | zero =>
    simp at H
    constructor
    . rfl
    . apply H
  | succ n => simp at H

theorem and_example2 (n m : Nat):
  n = 0 ∧ m = 0 -> n + m = 0
:= by
  intro ⟨h0, h1⟩
  rw [h0, h1]

theorem factor_is_0 (n m : Nat):
  n = 0 ∨ m = 0 -> n * m = 0
:= by
  intro H
  cases H with
  | inl h => rw [h]; simp
  | inr h => rw [h]; simp

theorem ex_falso_quodlibet (p: Prop):
  False -> p
:= by
  intros H
  cases H

def our_not (p : Prop) := p -> False

theorem not_implies_our_not (p: Prop):
  ¬ p -> (∀ q: Prop, p -> q)
:= by
  intros notp q H
  apply ex_falso_quodlibet
  apply notp
  apply H


theorem not_false':
  ¬ False
:= by
  intros H
  apply H

theorem zero_not_one:
  0 ≠ 1
:= by
  intros H
  cases H

theorem true_is_true:
  True
:= by
  simp
