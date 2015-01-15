module trustme where

open import eq

primitive
  primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

postulate
  A : Set
  x y : A

eq : x ≡ y
eq = primTrustMe




