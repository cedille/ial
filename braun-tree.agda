open import bool

module braun-tree (A : Set) (_<A_ : A → A → 𝔹) where

open import bool-thms
open import eq
open import list
open import nat
open import nat-thms
open import product
open import sum

-- the index n is the size of the tree (number of elements of type A)
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

-- helper for bt-remove-min
bt-remove-minh : ∀ {p n : ℕ} → braun-tree n → n ≡ (suc p) → A × braun-tree p
bt-remove-minh bt-empty ()
bt-remove-minh{p} (bt-node a bt-empty bt-empty u) e rewrite sym (suc-inj{0}{p} e) = a , bt-empty
bt-remove-minh{p} (bt-node a bt-empty (bt-node _ _ _ _) (inj₁ ()))
bt-remove-minh{p} (bt-node a bt-empty (bt-node _ _ _ _) (inj₂ ()))
bt-remove-minh{p} (bt-node a (bt-node{n1}{m1} a' l' r' u') bt-empty u) e rewrite sym (suc-inj{suc (n1 + m1 + 0)}{p} e) | +0 (n1 + m1) = 
  a , (bt-node a' l' r' u')
bt-remove-minh (bt-node a (bt-node{n1}{m1} a1 l1 r1 u1) (bt-node a2 l2 r2 u2) u) e with bt-remove-minh (bt-node a1 l1 r1 u1) refl
bt-remove-minh (bt-node a (bt-node{n1}{m1} a1 l1 r1 u1) (bt-node a2 l2 r2 u2) u) e | a1' , l1' 
  with if a1' <A a2  then (a1' , a2) else (a2 , a1')
bt-remove-minh{p} (bt-node a (bt-node{n1}{m1} a1 l1 r1 u1) (bt-node{n2}{m2} a2 l2 r2 u2) u) e | a1' , l1' | (smaller , other) 
  rewrite +suc (n1 + m1) (n2 + m2) | sym (suc-inj{suc (suc (n1 + m1 + (n2 + m2)))}{p} e) | +comm (n1 + m1) (n2 + m2) = 
  a , bt-node smaller (bt-node other l2 r2 u2) l1' (lem (n1 + m1) (n2 + m2) u)
  where lem : ∀ (x y : ℕ) → x =ℕ y ≡ tt ⊎ x =ℕ y + 1 ≡ tt → suc y =ℕ x ≡ tt ⊎ suc y =ℕ x + 1 ≡ tt
        lem x y (inj₁ u) rewrite =ℕ-to-≡{x}{y} u | +1 y = inj₂ (=ℕ-refl y)
        lem x y (inj₂ u) rewrite +1 y | =ℕ-sym x (suc y) = inj₁ u

-- remove the minimum (root) element from a nonempty tree, returning the element and the updated tree
bt-remove-min : ∀ {n : ℕ} → braun-tree (suc n) → A × braun-tree n
bt-remove-min t = bt-remove-minh t refl

-- this version stores data at the leaves instead of at the nodes
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