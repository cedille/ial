module stream2 where

open import bool
open import bool-thms
open import eq
open import level
open import nat
open import nat-thms
open import product
open import sum
open import vector
open import well-founded

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

{- If we have a stream 

      mk𝕊{k}{n} pre f 

   the meaning is that pre is a finite vector of the first k + n elements
   of the list, and f is a function that can take any vector of length k + n'
   and produce a vector with at least one new element (so the length of
   this vector is suc k', for some k').

   The finite prefix pre is stored with later elements first.  So the prefix

   13 ::𝕍 8 ::𝕍 5 ::𝕍 ::𝕍 3 ::𝕍 2 ::𝕍 1 ::𝕍 1 ::𝕍 0 ::𝕍 []𝕍

   could be a prefix for the Fibonacci stream.  The get function below
   will access the elements of this stream, for example, starting from 0
   (the earliest element).
-}
stream-update-func : ∀{ℓ}(A : Set ℓ) → ℕ → Set ℓ
stream-update-func A k = (∀ (n' : ℕ) → 𝕍 A (k + n') → Σ ℕ λ k' → 𝕍 A (suc k'))

data 𝕊 {ℓ}(A : Set ℓ) : ℕ → Set ℓ where
  mk𝕊 : ∀{k n : ℕ} →
         𝕍 A (k + n) → 
         stream-update-func A k → 
         𝕊 A (k + n)

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

--infixr 6 _::𝕊_
--infixr 5 _+𝕊ℕ_ 

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

{- This is a helper function for ensure.  It does course-of-values
   recursion on n ∸ n'. -}
ensureh : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (n' : ℕ) → WfStructBool _<_ (n' ∸ n) → 𝕊 A n → 
          Σ ℕ λ n'' → n' ≤ n'' ≡ tt ∧ 𝕊 A n''
ensureh{A = A} n' (WfStep fx) (mk𝕊{k = k}{n} pre f) with 𝔹-dec (n' ≤ k + n)
... | inj₁ p = ( k + n , p , (mk𝕊{k = k}{n} pre f))
... | inj₂ p with f n pre 
... | ( k' , l) with (l ++𝕍 pre) | ≤ff{n'} p
... | l' | p' rewrite +assoc k' k n | +comm k' k = ensureh n' (fx lem) (mk𝕊{k = k}{suc (k' + n)} l'' f)
                                         where lem : n' ∸ (k + suc (k' + n)) < n' ∸ (k + n) ≡ tt
                                               lem rewrite +suc k (k' + n) | +perm k k' n = ∸suc2 {n'} {k + n} {k'} p'
                                               l'' : 𝕍 A (k + suc (k' + n))
                                               l'' rewrite +suc k (k' + n) | +assoc k k' n = l'

{- take a stream that has n elements computed and turn it into one that 
   has at least n' elements. -}
ensure : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (n' : ℕ) → 𝕊 A n → 
           Σ ℕ λ n'' → n' ≤ n'' ≡ tt ∧ 𝕊 A n''
ensure{n = n} n' s = ensureh n' (wf-< (n' ∸ n)) s

{- given a stream with n elements, return the element at index n',
   where n' is less than n.  The indices count from the beginning of
   the stream (this is different from the beginning of the finite 
   prefix, which is stored with later elements of the stream first). -}
get : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (n' : ℕ) → n' < n ≡ tt → 𝕊 A n → A
get n' p (mk𝕊{k = k}{n} pre f) with <-implies-suc{n'} p
get n' p (mk𝕊{k = k}{n} pre f) | (y , u) = nth𝕍 ((k + n) ∸ (suc n')) (∸<{k + n} (lem u)) pre
                where lem : ∀{y} → k + n ≡ suc y → k + n =ℕ 0 ≡ ff
                      lem u rewrite u = refl

ensure-get : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (n' : ℕ) → 𝕊 A n → A
ensure-get n' s with ensure (suc n') s
... | (n'' , p , s') = get n' (suc≤<{n'} p) s'

all𝕊 : ∀ {ℓ} {A : Set ℓ}{n : ℕ}(p : ℕ → A → 𝔹) → 𝕊 A n → 𝔹
all𝕊 p (mk𝕊{k = k}{n} pre f) = all𝕍 p pre

{-
--------------------------------------------------
-- basic operations
--------------------------------------------------
head : ∀{ℓ}{A : Set ℓ} → 𝕊 A → A
head s = head𝕍 (s 1)

tail : ∀{ℓ}{A : Set ℓ} → 𝕊 A → 𝕊 A
tail s n = tail𝕍 (s (suc n))

_::𝕊_ : ∀{ℓ}{A : Set ℓ}{n : ℕ} → A → 𝕊 A → 𝕊 A 
(x ::𝕊 xs) 0 = [ x ]𝕍 
(x ::𝕊 xs) (suc o) = x ::𝕍 (xs o)


--------------------------------------------------
-- accessing a finite part of the stream
--------------------------------------------------

-- get the nth element
nth𝕊 : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → 𝕊 A → A
nth𝕊 n xs = head𝕍 (xs n)

-- return a vector of the first n+1 elements
take : ∀{ℓ}{A : Set ℓ} → (n : ℕ) → 𝕊 A → 𝕍 A (suc n)
take n xs = (xs n)

--------------------------------------------------
-- constructing basic streams
--------------------------------------------------

repeat : ∀{ℓ}{A : Set ℓ} → (a : A) → 𝕊 A
repeat a n = repeat𝕍 a (suc n) 

nats-from : ℕ → 𝕊 ℕ
nats-from x 0 = [ x ]𝕍
nats-from x (suc n) = x ::𝕍 nats-from (x + 1) n

nats : 𝕊 ℕ
nats = nats-from 0

--------------------------------------------------
-- creating new streams from old ones
--------------------------------------------------

foldl : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (B → A → B) → 𝕊 A → 𝕊 B
foldl b f xs n = foldl𝕍 b f (xs n)

map𝕊 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → 𝕊 A → 𝕊 B
map𝕊 f xs n = map𝕍 f (xs n)

zipWith : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → 
            (A → B → C) → 𝕊 A → 𝕊 B → 𝕊 C
zipWith f xs ys n = zipWith𝕍 f (xs n) (ys n)

_+𝕊ℕ_ : 𝕊 ℕ → 𝕊 ℕ → 𝕊 ℕ
_+𝕊ℕ_ = zipWith _+_ 

-}