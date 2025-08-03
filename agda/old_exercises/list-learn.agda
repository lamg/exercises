open import nat
open import eq
open import bool
open import nat-thms

data 𝕃 {l} (A : Set l) : Set l where
    [] : 𝕃 A
    _∷_ : (x : A) (xs : 𝕃 A) → 𝕃 A

[_] : ∀ {ℓ} {A : Set ℓ} → A → 𝕃 A
[ x ] = x ∷ []

length : ∀ {l}{A : Set l} → 𝕃 A → ℕ
length [] = 0
length (x ∷ xs) = length xs + 1

_++_ : ∀ {l} {A : Set l} → 𝕃 A → 𝕃 A → 𝕃 A
_++_ [] ys = ys
_++_ (x ∷ xs) ys = x ∷ (xs ++ ys)

++-length : ∀ {l} {A : Set l} (l0 l1 : 𝕃 A)
  → length (l0 ++ l1) ≡ length l0 + length l1
++-length [] l1 = refl
++-length (h ∷ t) l1 rewrite ++-length t l1 | +perm2 (length t) (length l1) 1 = refl

{-
length (l0 ++ l1) = length l0 + length l1
= { with l0 = h ∷ t1 }
length ((h ∷ t) ++ l1) = length (h ∷ t) ++ length l1
= { definition of ++ }
length (h ∷ (t ++ l1)) = length (h ∷ t) + length l1
= { definition of length }
suc (length (t ++ l1)) = suc (length t) + length l1
= { +-assoc }
suc (length (t ++ l1)) = suc (length t + length l1)
= { ++-length t l1 }
suc (length t + length l1) = suc (length t + length l1)
= { refl }
⊤
-}

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕃 A → 𝕃 B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

filter : ∀ {ℓ}{A : Set ℓ} → (A → 𝔹) → 𝕃 A → 𝕃 A
filter p [] = []
filter p (x ∷ xs) = let r = filter p xs in if p x then x ∷ r else r

remove : ∀ {ℓ}{A : Set ℓ} (eq : A → A → 𝔹)(a : A)(l : 𝕃 A) → 𝕃 A
remove eq a l = filter (λ x → ~ (eq a x)) l

data maybe {ℓ}(A : Set ℓ) : Set ℓ where
  just : A → maybe A
  nothing : maybe A

nth : ∀ {ℓ}{A : Set ℓ} → ℕ → 𝕃 A → maybe A
nth _ [] = nothing
nth 0 (x ∷ _) = just x
nth (suc n) (x ∷ xs) = nth n xs

sreverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
sreverse [] = []
sreverse (x ∷ xs) = sreverse xs ++ [ x ]

id-left-++ : ∀ {ℓ}{A : Set ℓ}(l : 𝕃 A) → [] ++ l ≡ l
id-left-++ l = refl

id-right-++ : ∀ {ℓ}{A : Set ℓ}(l : 𝕃 A) → l ++ [] ≡ l
id-right-++ [] = refl
id-right-++ (h ∷ t) rewrite id-right-++ t = refl

++-assoc : ∀ {ℓ}{A : Set ℓ} (l0 l1 l2 : 𝕃 A) → (l0 ++ l1) ++ l2 ≡ l0 ++ (l1 ++ l2)
++-assoc [] l1 l2 = refl
++-assoc (x ∷ xs) l1 l2 rewrite ++-assoc xs l1 l2 = refl

dist-sreverse : ∀ {ℓ}{A : Set ℓ}(a b : 𝕃 A)
  → sreverse (a ++ b) ≡ sreverse b ++ sreverse a
dist-sreverse [] b rewrite id-right-++ (sreverse b) = refl
dist-sreverse (h ∷ t) b rewrite dist-sreverse t b =
  ++-assoc (sreverse b) (sreverse t) (h ∷ [])

{-
sreverse (a ++ b) = sreverse b ++ sreverse a
sreverse (a ++ b)
= { a = (h ∷ t) }
sreverse ((h ∷ t) ++ b)
= { ++ def }
sreverse (h ∷ (t ++ b))
= { sreverse def }
sreverse (t ++ b) ++ [ h ]
= { assuming sreverse (t ++ b)}
sreverse b ++ sreverse t ++ [ h ]
= { sreverse def }
sreverse b ++ sreverse (h ∷ t)
= { a def }
sreverse b ++ sreverse a
-}

id-sreverse : ∀ {ℓ}{A : Set ℓ}(l : 𝕃 A) → sreverse (sreverse l) ≡ l
id-sreverse [] = refl
id-sreverse (x ∷ xs) rewrite dist-sreverse (sreverse xs) [ x ] | id-sreverse xs = refl

{-
sreverse (sreverse l)
= { l = (h ∷ t) }
sreverse (sreverse (h ∷ t))
= { sreverse def }
sreverse (sreverse t ++ [ h ])
= { sreverse dist }
sreverse [ h ] ++ sreverse (sreverse t)
= { assuming sreverse (sreverse t) }
sreverse [ h ] ++ t
= { sreverse [ h ] = [ h ]}
[ h ] ++ t
= { [ h ] ++ t = (h ∷ t) }
(h ∷ t)
= { l def }
l
-}

length-reverse : ∀ {ℓ}{A : Set ℓ}(l : 𝕃 A) → length (sreverse l) ≡ length l
length-reverse [] = refl
length-reverse (h ∷ t) rewrite ++-length (sreverse t) [ h ] | length-reverse t = refl

helper-reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A → 𝕃 A
helper-reverse xs [] = xs
helper-reverse xs (y ∷ ys) = helper-reverse (y ∷ xs) ys

reverse : ∀ {ℓ}{A : Set ℓ} → 𝕃 A → 𝕃 A
reverse l = helper-reverse [] l

+1-length : ∀ {ℓ}{A : Set ℓ}(h : A)(t : 𝕃 A) → length (h ∷ t) ≡ length t + 1
+1-length h [] = refl
+1-length h t = refl

length-helper-reverse : ∀ {ℓ}{A : Set ℓ}(xs ys : 𝕃 A)
  → length (helper-reverse xs ys) ≡ length xs + length ys
length-helper-reverse xs [] rewrite +0 (length xs) = refl
length-helper-reverse xs (h ∷ t)
  rewrite length-helper-reverse (h ∷ xs) t
  | +perm2 (length xs) 1 (length t)
  | +assoc (length xs) (length t) 1 = refl

length-preserve-reverse : ∀ {ℓ}{A : Set ℓ}(l : 𝕃 A)
  → length (reverse l) ≡ length l
length-preserve-reverse [] = refl
length-preserve-reverse (h ∷ t)
  rewrite length-helper-reverse [ h ] t | +1 (length t) = refl
