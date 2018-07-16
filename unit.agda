module unit where

open import level
open import eq

data ⊤ : Set where
  triv : ⊤

{-# COMPILE GHC ⊤ = data () (())  #-}

single-range : ∀{U : Set}{g : U → ⊤} → ∀{u : U} → g u ≡ triv
single-range {U}{g}{u} with g u
... | triv = refl
