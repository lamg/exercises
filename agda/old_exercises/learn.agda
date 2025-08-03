module learn where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + m = m
(suc n) + m = suc(n + m)

data even : ℕ → Set where
  ZERO : even zero
  STEP : ∀ x → even x → even (suc (suc x))

proof0 : even (suc (suc (suc (suc zero))))
proof0 = STEP (suc (suc zero)) (STEP zero ZERO)

proof1 : even (suc (suc zero))
proof1 = STEP zero ZERO

proofId : (A : Set) → A → A
proofId _ x = x

proofIdN : ℕ → ℕ
proofIdN = proofId ℕ

data _∧_ (P : Set) (Q : Set) : Set where
  ∧-intro : P → Q → (P ∧ Q)

weakening : {P Q : Set} → (P ∧ Q) → P
weakening (∧-intro p q) = p

_≡_ : (P : Set) → (Q : Set) → Set
a ≡ b = (a → b) ∧ (b → a)

∧-sym0 : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-sym0 (∧-intro p q) = (∧-intro q p)

∧-sym : {P Q : Set} → (P ∧ Q) ≡ (Q ∧ P)
∧-sym = ∧-intro ∧-sym0 ∧-sym0 

∧-assoc0 : {P Q R : Set} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc0 (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

∧-assoc1 : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc1 (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

∧-assoc : {P Q R : Set} → (P ∧ (Q ∧ R)) ≡ ((P ∧ Q) ∧ R)
∧-assoc = ∧-intro ∧-assoc0 ∧-assoc1


data _∨_ (P Q : Set) : Set where
  ∨-intro₀ : P → P ∨ Q
  ∨-intro₁ : Q → P ∨ Q

∨-sym0 : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-sym0 (∨-intro₀ p) = ∨-intro₁ p
∨-sym0 (∨-intro₁ q) = ∨-intro₀ q
  
-- ≡-def : {P Q : Set } → P ≡ Q ≡ P ∨ Q ≡ P ∧ Q

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥
