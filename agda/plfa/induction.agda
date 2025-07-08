import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = refl

+-assoc : ∀ ( m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p =
  begin
  (suc m + n) + p
  ≡⟨⟩
  (suc (m + n)) + p
  ≡⟨⟩ 
  suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
  suc (m + (n + p))
  ≡⟨⟩
  suc m + (n + p)
  ∎
