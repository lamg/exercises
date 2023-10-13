module repaso where

open import bool
open import eq

t0 : ∀ {a b c} → a ≡ b → a || c ≡ b || c 
t0 refl = refl

t1 : ∀ {a b c} → a ≡ b → a || c ≡ b || c
t1 p rewrite p = refl
