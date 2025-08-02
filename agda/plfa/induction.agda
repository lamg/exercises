import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = refl

+-assoc : ∀ (m n p : ℕ) -> (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl 

+-unit-right : ∀ (m : ℕ) → m + zero ≡ m
+-unit-right zero = refl
+-unit-right (suc m) rewrite +-unit-right m = refl 
  
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-symmetry : ∀ (m n : ℕ) → m + n ≡ n + m
+-symmetry m zero  =
  begin
  m + zero
  ≡⟨ +-unit-right m ⟩
  zero + m
  ∎
  
+-symmetry m (suc n)  =
  begin
  m + suc n
  ≡⟨ +-suc m n ⟩
  suc(m + n)
  ≡⟨ cong suc (+-symmetry m n) ⟩
  suc (n + m)
  ≡⟨ refl ⟩
  suc n + m
  ∎
