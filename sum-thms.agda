module sum-thms where

open import eq
open import sum

inj₁-inj : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{x : A}{x'} → inj₁{ℓ}{ℓ'}{A}{B} x ≡ inj₁ x' → x ≡ x'
inj₁-inj refl = refl