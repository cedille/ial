module string-thms where

open import bool
open import eq
open import string

postulate
  =string-refl : ∀(x : string) → x =string x ≡ tt