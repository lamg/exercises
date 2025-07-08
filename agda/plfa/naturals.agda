
open import plfa.part1.Naturals

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

_ : 2 + 4 ≡ 6
_ =
  begin
    2 + 4
    ≡⟨⟩
    6
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ suc m = n * (n ^ m)

_ : 3 ∸ 2 ≡ 1
_ = refl

_ : 2 ∸ 3 ≡ 0
_ = refl

