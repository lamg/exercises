open import nat
open import nat-thms

data 𝕍 {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  [] : 𝕍 A 0
  _∷_ : {n : ℕ} (x : A) (xs : 𝕍 A n) → 𝕍 A (suc n)

[_] : ∀ {ℓ} {A : Set ℓ} → A → 𝕍 A 1
[ x ] = x ∷ []

_++_ : ∀ {ℓ} {A : Set ℓ} {n m : ℕ} → 𝕍 A n → 𝕍 A m → 𝕍 A (n + m)
_++_ [] ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} { n : ℕ }
  → (A → B) → 𝕍 A n → 𝕍 B n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

