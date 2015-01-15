open import bool

module list-merge-sort (A : Set) (_<A_ : A → A → 𝔹) where

open import braun-tree A _<A_
open import eq
open import list
open import nat
open import nat-thms

merge : {n : ℕ}(l1 l2 : 𝕃 A) → n ≡ length l1 + length l2 → 𝕃 A
merge [] ys p = ys
merge xs [] p = xs
merge{0}(x :: xs) (y :: ys) ()
merge{suc n} (x :: xs) (y :: ys) p with x <A y
merge{suc n} (x :: xs) (y :: ys) p | tt = x :: (merge{n} xs (y :: ys) (suc-inj{n} p))
merge{suc n} (x :: xs) (y :: ys) p | ff = y :: (merge{n} (x :: xs) ys lem)
  where lem : n ≡ suc (length xs + length ys)
        lem rewrite sym (+suc (length xs) (length ys)) = suc-inj{n} p

merge-sort-h : ∀{n : ℕ} → braun-tree' n → 𝕃 A
merge-sort-h (bt'-leaf a) = [ a ]
merge-sort-h (bt'-node l r p) = merge (merge-sort-h l) (merge-sort-h r) refl

merge-sort : 𝕃 A → 𝕃 A
merge-sort [] = []
merge-sort (a :: as) with 𝕃-to-braun-tree' a as
merge-sort (a :: as) | t = merge-sort-h t
