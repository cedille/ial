open import bool
open import level
open import eq
open import product
open import product-thms
open import relations 

module closures where

  module basics {ℓ ℓ' : level}{A : Set ℓ} (_>A_ : A → A → Set ℓ') where

    data tc : A → A → Set (ℓ ⊔ ℓ') where
      tc-step : ∀{a b : A} → a >A b → tc a b
      tc-trans : ∀{a b c : A} → tc a b → tc b c → tc a c

    data rc : A → A → Set (ℓ ⊔ ℓ') where
      rc-step : ∀{a b : A} → a >A b → rc a b
      rc-refl : ∀{a : A} → rc a a
  
    tc-transitive : transitive tc
    tc-transitive = tc-trans 

  module combinations {ℓ ℓ' : level}{A : Set ℓ} (_>A_ : A → A → Set ℓ') where
     open basics

     rtc : A → A → Set (ℓ ⊔ ℓ')
     rtc = rc (tc _>A_)

  
    

