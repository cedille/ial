module stream-test where

open import bool
open import eq
open import nat
open import nat-thms
open import product
open import stream
open import stream-thms
open import vector

----------------------------------------------------------------------
-- basic tests
----------------------------------------------------------------------

test-map𝕊 = take 10 (map𝕊 (_+_ 10) nats)

----------------------------------------------------------------------
-- fibonacci sequence
----------------------------------------------------------------------

fib : 𝕊 ℕ
fib izero = 0
fib (isuc izero) = 1
fib (isuc (isuc o)) = (fib +𝕊ℕ (tail𝕊 fib)) o

test-fib = take 10 fib
test-fib2 = nth𝕊 8 fib

fibfasth : 𝕊 (ℕ × ℕ)
fibfasth izero = (0 , 1)
fibfasth (isuc o) with fibfasth o
... | ( a , b) = (b , a + b)

fibfast : 𝕊 ℕ
fibfast = map𝕊 fst fibfasth

{-
fib1h : ∀ {n:ℕ} → 𝕍 ℕ (suc n) → ℕi n → ℕ
fib1h (x :: xs) izero = x
fib1h (_ :: xs) (isuc o) = fib1h xs o


fib1 : 𝕊 ℕ
fib1 izero = 0
fib1 (isuc izero) = 1
fib1 (isuc (isuc o)) = fib1h (𝕊-to-𝕍 (fib1{suc n}))  =
... | x :: y :: xs  let s =  in
-}  


----------------------------------------------------------------------
-- Moessner's sequence
-- 
-- (moessner n) returns the stream of powers of n, although it is
-- a nontrivial theorem (not proved here) that this is truly what 
-- it does.
----------------------------------------------------------------------

{- (drop-every-h n N s) returns the stream which removes the n'th element
   of stream s (starting from 0), and after that removes every N'th element. -}
drop-every : ∀ {ℓ}{A : Set ℓ} → ℕ → ℕ → 𝕊 A → 𝕊 A
drop-every 0 N xs {d} izero = (head (tail𝕊 (xs{suc d})))
drop-every 0 N xs (isuc o) = drop-every N N (tail𝕊 (tail𝕊 xs)) o
drop-every (suc _) N xs {d} izero = (head (xs{d}))
drop-every (suc n) N xs (isuc o) = drop-every n N (tail𝕊 xs) o

ones = repeat𝕊 1
nats1 = nats-from 1

partial-sums : {n : ℕ} → 𝕊i ℕ n → 𝕊i ℕ n
partial-sums = foldl 0 _+_

drop-sum : ℕ → ℕ → 𝕊 ℕ → 𝕊 ℕ
drop-sum n N xs = partial-sums (drop-every n N xs)

moessner-h : ℕ → 𝕊 ℕ → 𝕊 ℕ 
moessner-h 0 xs = xs
moessner-h (suc n) xs = moessner-h n (drop-sum (suc n) n xs)

moessner : ℕ → 𝕊 ℕ
moessner n = moessner-h n ones

test-moessner = take 6 (moessner 2)

----------------------------------------------------------------------
-- nested calls
----------------------------------------------------------------------
φ : ∀{ℓ}{A : Set ℓ} {n : ℕ} (xs : 𝕊i A n) → 𝕊i A n
φ xs izero = xs izero
φ xs (isuc o) = (φ (φ (tail𝕊 xs))) o

φ-id : ∀{ℓ}{A : Set ℓ}{n : ℕ} (xs : 𝕊i A n) → φ xs =𝕊 xs
φ-id xs izero = refl
φ-id xs (isuc o) rewrite φ-id (φ (tail𝕊 xs)) o = φ-id (tail𝕊 xs) o

----------------------------------------------------------------------
-- Thue-Morse sequence
--
-- This follows the following definition from the paper "Productivity of 
-- Stream Definitions" by Endrullis et al.
--
--     M = 0:1:zip(tail𝕊(M), inv(tail𝕊(M)))
--
----------------------------------------------------------------------
thue-morse : 𝕊 𝔹 
thue-morse izero = ff
thue-morse (isuc izero) = tt
thue-morse{suc (suc n)} (isuc (isuc o)) = ((tail𝕊 (thue-morse{suc n})) ⋎ (map𝕊 (~_) (tail𝕊 (thue-morse{suc n})))) (≤2* n) o

test-thue-morse : take 10 thue-morse ≡ ff :: tt :: tt :: ff :: tt :: ff :: ff :: tt :: tt :: ff :: []
test-thue-morse = refl 


----------------------------------------------------------------------
-- Hamming stream
--
-- The sorted, duplicate-free list of all numbers n where the factors
-- of n are contained in {2,3,5}.
----------------------------------------------------------------------
merge : {n m : ℕ} → 𝕊i ℕ n → 𝕊i ℕ m → {k : ℕ} → k ≤ min n m ≡ tt → 𝕊i ℕ k
merge xs ys p izero with compare (head xs) (head ys)
... | compare-lt = (head xs) 
... | compare-gt = (head ys)
... | compare-eq = (head xs)
merge{suc n}{suc m} xs ys {suc k} p (isuc o) rewrite min-suc n m with compare (head xs) (head ys)
... | compare-lt = merge (tail𝕊 xs) ys (≤-trans{k} p (min-mono2 n m (suc m) (≤-suc m))) o
... | compare-gt = merge xs (tail𝕊 ys) (≤-trans{k} p (min-mono1 n (suc n) m (≤-suc n))) o
... | compare-eq = merge (tail𝕊 xs) (tail𝕊 ys) p o
merge{0}{suc m} xs ys () (isuc o)
merge{0}{0} xs ys () (isuc o)
merge{suc n}{0} xs ys () (isuc o)

hamming : 𝕊 ℕ
hamming izero = 1
hamming {suc n} (isuc o) = 
  merge (map𝕊 (_*_ 2) (hamming{n}))
        (merge (map𝕊 (_*_ 3) (hamming{n}))
               (map𝕊 (_*_ 5) (hamming{n})) 
               {min n n} (≤-refl (min n n))) lem o
   where lem : n ≤ min n (min n n) ≡ tt
         lem rewrite min-same n | <-irrefl n | ≤-refl n = refl

test-hamming = take 12 hamming


