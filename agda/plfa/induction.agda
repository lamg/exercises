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

+-unit-right : ∀ (m : ℕ) → m + zero ≡ m
+-unit-right zero = refl
+-unit-right (suc m) =
  begin
  suc m + zero
  ≡⟨⟩
  suc (m + zero)
  ≡⟨ cong suc (+-unit-right m) ⟩
  suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n =
  begin
  suc m + suc n
  ≡⟨⟩
  suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
  suc (suc (m + n))
  ∎

+-symmetry : ∀ (m n : ℕ) → m + n ≡ n + m
+-symmetry zero n =  {! !}
+-symmetry (suc m) n = {!!}
