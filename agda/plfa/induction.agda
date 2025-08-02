import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
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
+-symmetry zero n rewrite +-unit-right n =  refl
+-symmetry (suc m) n rewrite +-suc n m = cong suc (+-symmetry m n)
