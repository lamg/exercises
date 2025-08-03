module verified where

open import bool
open import eq

fofo : 𝔹
fofo = tt && ff

my-elim : ∀(b : 𝔹) → ~ ~ b ≡ b
my-elim tt = refl
my-elim ff = refl

&&-idem : ∀ {b} → b && b ≡ b
&&-idem {tt} = refl
&&-idem {ff} = refl

&&-idem-test : tt && tt ≡ tt
&&-idem-test = &&-idem

||-unit : ∀ {b} → ff || b ≡ b
||-unit {p} = refl

&&-unit : ∀ {b} → tt && b ≡ b
&&-unit {p} = refl

||-zero : ∀ {b} → tt || b ≡ tt
||-zero {p} = refl

&&-zero : ∀ {b} → ff && b ≡ ff
&&-zero {p} = refl

id : ∀ {a b : 𝔹} → a ≡ b → a ≡ b
id refl = refl

golden-rule : ∀(a b : 𝔹) → (a || b) ≡ (a && b) → a ≡ b
golden-rule ff p rewrite &&-zero{ff} = sym
golden-rule tt p rewrite ||-zero{tt} = id

strengthening : ∀ {a b} → (a || b ≡ ff) → (a ≡ ff)
strengthening {ff} x = refl
strengthening {tt} ()

f0 : ff && ff ≡ ~ tt
f0 = refl

f1 : ∀ {x} → x && tt ≡ x
f1 {tt} = refl
f1 {ff} = refl

f2 : ∀{x} → x && tt ≡ x
f2 {tt} = refl
f2 {ff} = refl

--- chapter 3

open import nat

+-unit : ∀ (x : ℕ) → 0 + x ≡ x
+-unit x = refl

+-unit-r : ∀ (x : ℕ) → x + 0 ≡ x
+-unit-r zero = refl
+-unit-r (suc n) rewrite +-unit-r n = refl

-- suc n + 0 ≡ suc n
-- = {def _+_ (I believe Agda is helping with this) }
-- suc (n + 0) ≡ suc n
-- = { rewrite n + 0 ≡ n}
-- suc n ≡ suc n
-- = { refl }
-- ⊤

-- rewrite +-unit-r n
-- =
-- rewrite n + 0 ≡ n

assoc : ∀ (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
assoc 0 p q    = refl
assoc (suc n) p q rewrite assoc n p q = refl

-- suc n + (p + q) ≡ (suc n + p) + q
-- = { _+_ }
-- suc (n + (p + q)) = suc (n + p) + q
-- = { _+_ }
-- suc (n + (p + q)) = suc ((n + p) + q)
-- = { rewrite n + (p + q) ≡ (n + p) + q}
-- suc ((n + p) + q) = suc ((n + p) + q)
-- = { refl }
-- ⊤


+suc : ∀ (x y : ℕ) → x + (suc y) ≡ suc (x + y)
+suc zero y = refl
+suc (suc x) y rewrite +suc x y = refl

-- +suc x y
-- = { rewrite }
-- x + suc y ≡ suc (x + y)

-- _+_ : ℕ → ℕ → ℕ
-- zero  + n = n
-- suc m + n = suc (m + n)

-- suc x + suc y ≡ suc (suc x + y)
-- = { _+_ }
-- suc (x + suc y) ≡ suc (suc (x + y))
-- = { rewrite +suc x y }
-- suc (suc (x + y)) ≡ suc (suc (x + y))
-- = { refl }
-- ⊤

sym+ : ∀ (x y : ℕ) → x + y ≡ y + x
sym+ zero q rewrite +-unit-r q = refl
sym+ (suc p) q rewrite +suc q p | sym+ p q  = refl

-- +suc q p
-- = { +suc }
-- q + suc p ≡ suc (q + p)

-- sym+ p q
-- = { sym+ }
-- p + q = q + p

-- +-unit-r q
-- = { +-unit-r }
-- q + 0 ≡ q

-- zero + q ≡ q + zero
-- = { rewrite +-unit-r }
-- zero + q ≡ q
-- = { _+_.0 }
-- q ≡ q
-- = { refl }
-- ⊤ 

-- suc p + q ≡ q + suc p
-- = { _+_.1 }
-- suc (p + q) ≡ q + suc p
-- = {rewrite +suc q p}
-- suc (p + q) ≡ suc (q + p)
-- = {rewrite +sym p q}
-- suc (q + p) ≡ suc (q + p)
-- = { refl }
-- ⊤

*-dist : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*-dist zero n p = refl
*-dist (suc m) n p rewrite *-dist m n p  = assoc p (m * p) (n * p)

*-dist' : ∀ (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
*-dist' zero n p = refl
*-dist' (suc m) n p rewrite *-dist' m n p | assoc p (m * p) (n * p) = refl

-- (zero + n) * p ≡ zero * p + n * p
-- = { _+_.0 }
-- n * p ≡ zero * p + n * p
-- = { _*_.0 }
-- n * p ≡ zero + n * p
-- = { _+_.0 }
-- n * p ≡ n * p
-- = { refl }
-- ⊤

-- (suc m + n) * p
-- = { _+_ }
-- (suc (m + n)) * p
-- = { _*_ }
-- p + (m + n) * p


-- (suc m) * p + n * p
-- = { _*_ }
-- (p + m * p) + n * p
-- = { rewrite assoc p (m * p) (n * p) }
-- p + (m * p + n * p)
-- = { rewrite *-dist m n p }
-- p + (m + n) * p

*-zero-r : ∀ (n : ℕ) → n * zero ≡ zero
*-zero-r zero = refl
*-zero-r (suc n) = *-zero-r n

*suc : ∀ (a b : ℕ) → a * suc b ≡ a + a * b
*suc zero m rewrite *-zero-r m = refl
*suc (suc n) m rewrite
  *suc n m | assoc m n (n * m) | assoc n m (n * m) | sym+ n m = refl

*-sym : ∀ (a b : ℕ) → a * b ≡ b * a
*-sym zero n rewrite *-zero-r n = refl
*-sym (suc m) n rewrite *suc n m | *-sym n m = refl


-- suc m * n ≡ n * suc m
-- = { _*_ }
-- n + m * n ≡ n * suc m
-- = { *suc }
-- n + m * n = n + m * n

-- <-trans : ∀ {x y z : ℕ} → x < y ≡ tt → y < z ≡ tt → x < z ≡ tt
-- <-trans zero y z = ? 
