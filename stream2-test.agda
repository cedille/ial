module stream2-test where

open import bool
open import eq
open import nat
open import nat-thms
open import product
open import stream2
open import vector

----------------------------------------------------------------------
-- basic tests
----------------------------------------------------------------------

-- test-map𝕊 = take 10 (map𝕊 (_+_ 10) nats)

----------------------------------------------------------------------
-- fibonacci sequence
----------------------------------------------------------------------


fib : 𝕊 ℕ 2
fib = (mk𝕊{k = 2} (1 :: 0 :: []) fib-grow)
      where fib-grow : ∀ (n : ℕ) → 𝕍 ℕ (2 + n) → Σ ℕ λ k' → 𝕍 ℕ (suc k')
            fib-grow n (x :: y :: _) = (0 , [ x + y ]𝕍)
           
test = ensure 10 fib

{-
fib-mono : ∀ {n : ℕ} → 0 < ensure-get (suc n) fib ≡ tt
fib-mono{0} = refl
fib-mono{suc n} = {!!}-}