-- an example showing how to use sigma types to define a type for non-zero natural numbers
module nat-nonzero where

open import bool
open import eq
open import nat
open import product

ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → iszero n ≡ ff)

suc⁺ : ℕ⁺ → ℕ⁺ 
suc⁺ (zero , ())
suc⁺ (suc n1 , p) = suc (suc n1) , refl

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(zero , ()) +⁺ n2 
(1 , p1) +⁺ y = suc⁺ y
(suc (suc n1) , p1) +⁺ y = suc⁺ ((suc n1 , refl) +⁺ y)