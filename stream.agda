module stream where

open import bool
open import eq
open import level
open import nat
open import nat-thms
open import vector

----------------------------------------------------------------------
-- datatypes
----------------------------------------------------------------------

-- sized indices into the stream
data ℕi : ℕ → Set where
  izero : {n : ℕ} → ℕi n
  isuc : {n : ℕ} → ℕi n → ℕi (suc n)

-- 𝕊i A n is the type for streams of A elements which can accept indices of size at most n.
𝕊i : ∀{ℓ}→ Set ℓ → ℕ → Set ℓ
𝕊i A n = ℕi n → A

-- 𝕊 A is the type for streams supporting indices of any size.
𝕊 : ∀{ℓ}→ Set ℓ → Set ℓ
𝕊 A = ∀ {n : ℕ} → 𝕊i A n

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixr 6 _::𝕊_
infixr 5 _+𝕊ℕ_ _⋎_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

ℕ-to-ℕi : ∀ (n : ℕ) → ℕi n
ℕ-to-ℕi zero = izero
ℕ-to-ℕi (suc n) = isuc (ℕ-to-ℕi n)

--------------------------------------------------
-- basic operations
--------------------------------------------------
head : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕊i A n → A
head s = s izero

tail : ∀{ℓ}{A : Set ℓ}{n : ℕ} → 𝕊i A (suc n) → 𝕊i A n
tail s o = s (isuc o)

_::𝕊_ : ∀{ℓ}{A : Set ℓ}{n : ℕ} → A → 𝕊i A n → 𝕊i A (suc n)
(x ::𝕊 xs) izero = x
(x ::𝕊 xs) (isuc o) = xs o

--------------------------------------------------
-- accessing a finite part of the stream
--------------------------------------------------

-- get the nth element
nth𝕊 : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → 𝕊i A n → A
nth𝕊 n xs = xs (ℕ-to-ℕi n)

-- return a vector of all the elements in a depth-bounded stream
𝕊-to-𝕍 : ∀{ℓ}{A : Set ℓ} {n : ℕ} → 𝕊i A n → 𝕍 A (suc n)
𝕊-to-𝕍{n = 0} xs = [ head xs ]𝕍
𝕊-to-𝕍{n = suc n} xs = (head xs) :: (𝕊-to-𝕍 (tail xs))

-- take n elements from a stream with depth-bound n
take : ∀{ℓ}{A : Set ℓ} → (n : ℕ) → 𝕊i A n → 𝕍 A n
take 0 xs = []
take (suc n) xs = (head xs) :: (take n (tail xs))

--------------------------------------------------
-- constructing basic streams
--------------------------------------------------

repeat𝕊 : ∀{ℓ}{A : Set ℓ} → (a : A) → 𝕊 A
repeat𝕊 a izero = a
repeat𝕊 a (isuc o) = repeat𝕊 a o


nats-from : ℕ → 𝕊 ℕ
nats-from x izero = x
nats-from x (isuc o) = nats-from (x + 1) o

nats : 𝕊 ℕ
nats = nats-from 0

--------------------------------------------------
-- creating new streams from old ones
--------------------------------------------------

foldl : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → B → (B → A → B) → {n : ℕ} → 𝕊i A n → 𝕊i B n
foldl b _f_ xs izero = (b f (head xs))
foldl b _f_ xs (isuc o) = (foldl (b f (head xs)) _f_ (tail xs) o)

map𝕊 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → {n : ℕ} → 𝕊i A n → 𝕊i B n
map𝕊 f xs izero = (f (head xs))
map𝕊 f xs (isuc o) = (map𝕊 f (tail xs) o)

zipWith : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''} → 
            (A → B → C) → {n : ℕ} → 𝕊i A n → 𝕊i B n → 𝕊i C n
zipWith _f_ xs ys izero = (head xs) f (head ys)
zipWith _f_ xs ys (isuc o) = zipWith _f_ (tail xs) (tail ys) o

_+𝕊ℕ_ : {n : ℕ} → 𝕊i ℕ n → 𝕊i ℕ n → 𝕊i ℕ n
_+𝕊ℕ_ = zipWith _+_ 

_⋎_ : ∀ {ℓ} {A : Set ℓ} → {n : ℕ} → 𝕊i A n → 𝕊i A n → {k : ℕ} → k ≤ 2 * n ≡ tt → 𝕊i A k
(xs ⋎ ys) p izero = (head xs) 
(xs ⋎ ys) p (isuc izero) = (head ys)
_⋎_ {n = suc n} xs ys {suc (suc k)} p (isuc (isuc o)) rewrite +suc n (n + 0) = ((tail xs) ⋎ (tail ys)) p o
_⋎_ {n = 0} xs ys {suc (suc k)} () _
