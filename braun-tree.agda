open import bool

module braun-tree{ℓ} (A : Set ℓ) (_<A_ : A → A → 𝔹) where

open import bool-thms
open import eq
open import list
open import nat
open import nat-thms
open import product
open import sum

-- the index n is the size of the tree (number of elements of type A)
data braun-tree : (n : ℕ) → Set ℓ where
  bt-empty : braun-tree 0
  bt-node : ∀ {n m : ℕ} → 
            A → braun-tree n → braun-tree m → 
            n ≡ m ∨ n ≡ suc m → 
            braun-tree (suc (n + m))

{- we will keep smaller (_<A_) elements closer to the root of the Braun tree as we insert -}
bt-insert : ∀ {n : ℕ} → A → braun-tree n → braun-tree (suc n)
bt-insert a bt-empty = bt-node a bt-empty bt-empty (inj₁ refl)
bt-insert a (bt-node{n}{m} a' l r p) 
  rewrite +comm n m with p | if a <A a' then (a , a') else (a' , a)
bt-insert a (bt-node{n}{m} a' l r _) | inj₁ p | (a1 , a2) 
  rewrite p = (bt-node a1 (bt-insert a2 r) l (inj₂ refl))
bt-insert a (bt-node{n}{m} a' l r _) | inj₂ p | (a1 , a2) = 
  (bt-node a1 (bt-insert a2 r) l (inj₁ (sym p)))

bt-remove-min : ∀ {p : ℕ} → braun-tree (suc p) → A × braun-tree p
bt-remove-min (bt-node a bt-empty bt-empty u) = a , bt-empty
bt-remove-min (bt-node a bt-empty (bt-node _ _ _ _) (inj₁ ()))
bt-remove-min (bt-node a bt-empty (bt-node _ _ _ _) (inj₂ ()))
bt-remove-min (bt-node a (bt-node{n'}{m'} a' l' r' u') bt-empty u) rewrite +0 (n' + m') = a , bt-node a' l' r' u'
bt-remove-min (bt-node a (bt-node a1 l1 r1 u1) (bt-node a2 l2 r2 u2) u) with bt-remove-min (bt-node a1 l1 r1 u1) 
bt-remove-min (bt-node a (bt-node a1 l1 r1 u1) (bt-node a2 l2 r2 u2) u) | a1' , l' 
  with if a1' <A a2  then (a1' , a2) else (a2 , a1')
bt-remove-min (bt-node a (bt-node{n1}{m1} a1 l1 r1 u1) (bt-node{n2}{m2} _ l2 r2 u2) u) | _ , l' | smaller , other 
  rewrite +suc (n1 + m1) (n2 + m2) | +comm (n1 + m1) (n2 + m2) = a , bt-node smaller (bt-node other l2 r2 u2) l' (lem u) 
  where lem : ∀{x y} → suc x ≡ y ∨ suc x ≡ suc y → y ≡ x ⊎ y ≡ suc x
        lem (inj₁ p) = inj₂ (sym p)
        lem (inj₂ p) = inj₁ (sym (suc-inj p))

----------------------------------------------------------------------
-- this version stores data at the leaves instead of at the nodes
----------------------------------------------------------------------
data braun-tree' : (n : ℕ) → Set ℓ where
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