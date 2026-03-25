-- mathematical integers; see int.agda for imported machine integers from Haskell.
module integer where

open import bool
open import bool-thms2
open import eq
open import nat
open import nat-thms
open import product
open import product-thms
open import sum
open import unit

ℤ-pos-t : ℕ → Set
ℤ-pos-t 0 = ⊤
ℤ-pos-t (suc _) = 𝔹

{- In mkℤ n a, the argument a tells whether the integer is positive or negative, if n is nonzero.
   If n is zero, then a is just triv : ⊤, so there is a unique integer value for 0. -}
data ℤ : Set where
  mkℤ : (n : ℕ) → ℤ-pos-t n → ℤ

infixl 9 _+ℤ_ _-ℤ_
infixl 8 _≤ℤ_ 

0ℤ : ℤ
0ℤ = mkℤ 0 triv

1ℤ : ℤ
1ℤ = mkℤ 1 tt

-1ℤ : ℤ
-1ℤ = mkℤ 1 ff

toℤ : ℕ → ℤ
toℤ 0 = 0ℤ
toℤ (suc x) = mkℤ (suc x) tt

abs-val : ℤ → ℕ
abs-val (mkℤ n _) = n

negℤ : ℤ → ℤ
negℤ (mkℤ 0 triv) = mkℤ 0 triv
negℤ (mkℤ (suc n) b) = mkℤ (suc n) (~ b)

is-evenℤ : ℤ → 𝔹
is-evenℤ (mkℤ n _) = is-even n

is-oddℤ : ℤ → 𝔹
is-oddℤ (mkℤ n _) = is-odd n

{- subtract the second natural number from the first, returning an integer.
   This is mostly a helper for _+ℤ_ -}
diffℤ : ℕ → ℕ → ℤ
diffℤ n m with ℕ-trichotomy n m 
diffℤ n m | inj₁ p with <∸suc{m}{n} p               -- n < m
diffℤ n m | inj₁ p | x , _ = mkℤ (suc x) ff
diffℤ n m | inj₂ (inj₁ p) = mkℤ 0 triv              -- n = m 
diffℤ n m | inj₂ (inj₂ p) with <∸suc{n}{m} p
diffℤ n m | inj₂ (inj₂ p) | x , _ = mkℤ (suc x) tt  -- m < n 

_+ℤ_ : ℤ → ℤ → ℤ
(mkℤ 0 _) +ℤ x = x
x +ℤ (mkℤ 0 _) = x
(mkℤ (suc n) p1) +ℤ (mkℤ (suc m) p2) with p1 xor p2 
(mkℤ (suc n) p1) +ℤ (mkℤ (suc m) p2) | ff = mkℤ (suc n + suc m) p1
(mkℤ (suc n) p1) +ℤ (mkℤ (suc m) p2) | tt = if p1 imp p2 then diffℤ m n else diffℤ n m 

_-ℤ_ : ℤ → ℤ → ℤ
x -ℤ y = x +ℤ (negℤ y)

test-+ℤ1 : (mkℤ 2 ff) +ℤ (mkℤ 4 tt) ≡ (mkℤ 2 tt)
test-+ℤ1 = refl

test-+ℤ2 : (mkℤ 2 tt) +ℤ (mkℤ 4 ff) ≡ (mkℤ 2 ff)
test-+ℤ2 = refl

_≤ℤ_ : ℤ → ℤ → 𝔹
(mkℤ 0 triv) ≤ℤ (mkℤ 0 triv) = tt
(mkℤ 0 triv) ≤ℤ (mkℤ (suc _) pos) = pos
(mkℤ (suc _) pos) ≤ℤ (mkℤ 0 triv) = ~ pos
(mkℤ (suc x) pos1) ≤ℤ (mkℤ (suc y) pos2) with pos1 xor pos2
(mkℤ (suc x) pos1) ≤ℤ (mkℤ (suc y) pos2) | tt = pos1 imp pos2
(mkℤ (suc x) pos1) ≤ℤ (mkℤ (suc y) pos2) | ff = if pos1 then x ≤ y else y ≤ x

≤ℤ-antisymm : ∀(x y : ℤ) → x ≤ℤ y ≡ tt → y ≤ℤ x ≡ tt → x ≡ y
≤ℤ-antisymm (mkℤ zero triv) (mkℤ zero triv) p q = refl
≤ℤ-antisymm (mkℤ zero triv) (mkℤ (suc y) pos2) p q rewrite p with q 
≤ℤ-antisymm (mkℤ zero triv) (mkℤ (suc y) pos2) p q | ()
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ zero triv) p q rewrite q with p
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ zero triv) p q | ()
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q with keep (pos1 xor pos2)
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q | tt , rp rewrite rp | xor-comm pos1 pos2 | rp with imp-antisymm{pos1} p q 
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q | tt , rp | pp rewrite pp | xor-anti-idem pos2 with rp
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q | tt , rp | pp | ()
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q | ff , rp
 rewrite rp | xor-comm pos1 pos2 | rp | xor-≡{pos2}rp with pos1 
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q | ff , rp | tt rewrite ≤-antisym{x} p q = refl
≤ℤ-antisymm (mkℤ (suc x) pos1) (mkℤ (suc y) pos2) p q | ff , rp | ff rewrite ≤-antisym{y} p q = refl

+ℤ0 : ∀{z : ℤ} → z +ℤ 0ℤ ≡ z
+ℤ0 {mkℤ zero triv} = refl
+ℤ0 {mkℤ (suc n) tt} = refl
+ℤ0 {mkℤ (suc n) ff} = refl

toℤ-≤ : ∀{n m : ℕ} → toℤ n ≤ℤ toℤ m ≡ tt → n ≤ m ≡ tt
toℤ-≤ {zero} {zero} p = refl
toℤ-≤ {zero} {suc m} p = refl
toℤ-≤ {suc n} {suc m} p = p

