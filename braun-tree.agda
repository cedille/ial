open import bool

module braun-tree (A : Set) (_<A_ : A → A → 𝔹) where

open import bool-thms
open import eq
open import list
open import nat
open import nat-thms
open import product
open import sum

data braun-tree : (n : ℕ) → Set where
  bt-empty : braun-tree 0
  bt-node : ∀ {n m : ℕ} → 
            A → braun-tree n → braun-tree m → 
            n =ℕ m ≡ tt ∨ n =ℕ m + 1 ≡ tt → 
            braun-tree (1 + n + m)

{- we will keep smaller (_<A_) elements closer to the root of the Braun tree as we insert -}
bt-insert : ∀ {n : ℕ} → A → braun-tree n → braun-tree (suc n)
bt-insert a bt-empty = bt-node a bt-empty bt-empty (inj₁ refl)
bt-insert a (bt-node{n}{m} a' l r p) 
  rewrite +comm n m with p | if a <A a' then (a , a') else (a' , a)
bt-insert a (bt-node{n}{m} a' l r p) | inj₁ p' | (a1 , a2)
  rewrite =ℕ-to-≡{n} p' = (bt-node a1 (bt-insert a2 r) l (inj₂ lem))
  where lem : suc m =ℕ m + 1 ≡ tt
        lem rewrite +comm m 1 = =ℕ-refl m 
bt-insert a (bt-node{n}{m} a' l r p) | inj₂ p' | (a1 , a2) =
  (bt-node a1 (bt-insert a2 r) l (inj₁ (lem n m p')))
  where lem : ∀ n m → n =ℕ m + 1 ≡ tt → suc m =ℕ n ≡ tt
        lem n m p' rewrite =ℕ-to-≡{n} p' | +comm m 1 = =ℕ-refl m




data braun-tree' : (n : ℕ) → Set where
  bt'-leaf : A → braun-tree' 1
  bt'-node : ∀ {n m : ℕ} → 
            braun-tree' n → braun-tree' m → 
            n =ℕ m ≡ tt ⊎ n =ℕ m + 1 ≡ tt → 
            braun-tree' (n + m)

bt'-insert : ∀ {n : ℕ} → A → braun-tree' n → braun-tree' (suc n)
bt'-insert a (bt'-leaf a') = bt'-node (bt'-leaf a) (bt'-leaf a') (inj₁ refl)
bt'-insert a (bt'-node{n}{m} l r p) rewrite +comm n m with p 
bt'-insert a (bt'-node{n}{m} l r p) | inj₁ p' rewrite =ℕ-to-≡{n} p' = (bt'-node (bt'-insert a r) l (inj₂ lem))
  where lem : suc m =ℕ m + 1 ≡ tt
        lem rewrite +comm m 1 = =ℕ-refl m 
bt'-insert a (bt'-node{n}{m} l r p) | inj₂ p' = (bt'-node (bt'-insert a r) l (inj₁ (lem n m p')))
  where lem : ∀ n m → n =ℕ m + 1 ≡ tt → suc m =ℕ n ≡ tt
        lem n m p' rewrite =ℕ-to-≡{n} p' | +comm m 1 = =ℕ-refl m
  
𝕃-to-braun-tree' : A → (l : 𝕃 A) → braun-tree' (suc (length l))
𝕃-to-braun-tree' a [] = bt'-leaf a
𝕃-to-braun-tree' a (a' :: as) = bt'-insert a (𝕃-to-braun-tree' a' as)