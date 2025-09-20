theorem specialize_example:
  ∀ n: Nat, (∀ m, m * n = 0) -> n = 0
:= by
  intros n h
  specialize h 1
  simp at h
  apply h
