module product-thms where

open import eq
open import level
open import product

-- this is called the inspect idiom, in the Agda stdlib
keep : ∀{ℓ}{A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
keep x = ( x , refl )