{- definition of a triangle property for triples of relations -}

open import product
open import rel
open import rtc

module triangle where

triangle : ∀{A : Set}(r1 : Rel A)(r2 : Rel A)(r3 : Rel A) → Set
triangle{A} r1 r2 r3 = ∀ {x y z : A} → r1 x y → r2 x z → r3 y z

