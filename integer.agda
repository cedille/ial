-- mathematical integers; see int.agda for imported machine integers from Haskell.
module integer where

open import bool
open import eq
open import nat
open import nat-thms
open import product
open import product-thms
open import sum
open import unit

ℤ-pos-t : nat → Set
ℤ-pos-t 0 = ⊤
ℤ-pos-t (suc n) = 𝔹

{- In mkℤ n a, the argument a tells whether the integer is positive or negative, if n is nonzero.
   If n is zero, then a is just triv : ⊤, so there is a unique integer value for 0. -}
data ℤ : Set where
  mkℤ : (n : nat) → ℤ-pos-t n → ℤ

0ℤ : ℤ
0ℤ = mkℤ 0 triv

1ℤ : ℤ
1ℤ = mkℤ 1 tt

-1ℤ : ℤ
-1ℤ = mkℤ 1 ff

-- helper for addition
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
(mkℤ (suc n) tt) +ℤ (mkℤ (suc m) tt) = mkℤ (suc n + suc m) tt
(mkℤ (suc n) tt) +ℤ (mkℤ (suc m) ff) = diffℤ n m 
(mkℤ (suc n) ff) +ℤ (mkℤ (suc m) tt) = diffℤ m n 
(mkℤ (suc n) ff) +ℤ (mkℤ (suc m) ff) = mkℤ (suc n + suc m) ff

test-+ℤ1 : (mkℤ 2 ff) +ℤ (mkℤ 4 tt) ≡ (mkℤ 2 tt)
test-+ℤ1 = refl

test-+ℤ2 : (mkℤ 2 tt) +ℤ (mkℤ 4 ff) ≡ (mkℤ 2 ff)
test-+ℤ2 = refl