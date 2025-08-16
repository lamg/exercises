
theorem and_comm_forward (p q : Prop): p ∧ q → q ∧ p := by
  intro h
  apply And.intro
  . apply h.right
  . apply h.left
