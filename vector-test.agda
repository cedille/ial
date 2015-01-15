module vector-test where

open import bool
open import list
open import vector

test-vector : 𝕃 (𝕍 𝔹 2)
test-vector = (ff :: tt :: []) :: (tt :: ff :: []) :: (tt :: ff :: []) :: []

