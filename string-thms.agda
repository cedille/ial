module string-thms where

open import bool
open import eq
open import string

postulate
  =string-refl : (s : string) → s =string s ≡ tt
