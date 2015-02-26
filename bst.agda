-- binary search trees (not balanced)

open import bool
open import eq
open import product
open import product-thms

module bst (A : Set) (_≤A_ : A → A → 𝔹)
           (≤A-refl : ∀ {a : A} → a ≤A a ≡ tt)
           (≤A-trans : ∀ {a b c : A} → a ≤A b ≡ tt → b ≤A c ≡ tt → a ≤A c ≡ tt)
           (≤A-total : ∀ {a b : A} → a ≤A b ≡ ff → b ≤A a ≡ tt) where

data bst : A → A → Set where
  bst-leaf : ∀ {l u : A} → l ≤A u ≡ tt → bst l u
  bst-node : ∀ {l l' u' u : A}(d : A) → 
               bst l' d → bst d u' → 
               l ≤A l' ≡ tt → u' ≤A u ≡ tt → 
               bst l u

{- at some point this private development of min and max based on the
   generic ordering _≤A_ could be abstracted out into its own module
   elsewhere (and maybe apply for max/min theorems in nat-thms.agda?) -}
private

  min : A → A → A
  min = λ x y → if x ≤A y then x else y

  max : A → A → A
  max = λ x y → if x ≤A y then y else x

  min1-≤A : ∀{x y : A} → min x y ≤A x ≡ tt
  min1-≤A{x}{y} with keep (x ≤A y)
  min1-≤A{x}{y} | tt , p rewrite p = ≤A-refl
  min1-≤A{x}{y} | ff , p rewrite p = ≤A-total p 

  min2-≤A : ∀{x y : A} → min x y ≤A y ≡ tt
  min2-≤A{x}{y} with keep (x ≤A y)
  min2-≤A{x}{y} | tt , p rewrite p = p
  min2-≤A{x}{y} | ff , p rewrite p = ≤A-refl

  max1-≤A : ∀{x y : A} → x ≤A max x y ≡ tt
  max1-≤A{x}{y} with keep (x ≤A y)
  max1-≤A{x}{y} | tt , p rewrite p = p
  max1-≤A{x}{y} | ff , p rewrite p = ≤A-refl

  max2-≤A : ∀{x y : A} → y ≤A max x y ≡ tt
  max2-≤A{x}{y} with keep (x ≤A y)
  max2-≤A{x}{y} | tt , p rewrite p = ≤A-refl
  max2-≤A{x}{y} | ff , p rewrite p = ≤A-total p

  min1-mono : ∀{x x' y : A} → x ≤A x' ≡ tt → min x y ≤A min x' y ≡ tt
  min1-mono{x}{x'}{y} p with keep (x ≤A y) | keep (x' ≤A y)
  min1-mono p | tt , q | tt , q' rewrite q | q' = p
  min1-mono p | tt , q | ff , q' rewrite q | q' = q
  min1-mono p | ff , q | tt , q' rewrite q | q' | ≤A-trans p q' with q 
  min1-mono p | ff , q | tt , q' | ()
  min1-mono p | ff , q | ff , q' rewrite q | q' = ≤A-refl

  max2-mono : ∀{x y y' : A} → y ≤A y' ≡ tt → max x y ≤A max x y' ≡ tt
  max2-mono{x}{y}{y'} p with keep (x ≤A y) | keep (x ≤A y')
  max2-mono p | tt , q | tt , q' rewrite q | q' = p
  max2-mono p | tt , q | ff , q' rewrite q | q' = ≤A-trans p (≤A-total q')
  max2-mono p | ff , q | tt , q' rewrite q | q' = q'
  max2-mono p | ff , q | ff , q' rewrite q | q' = ≤A-refl

bst-dec-lb : ∀ {l l' u' : A} → bst l' u' → l ≤A l' ≡ tt → bst l u'
bst-dec-lb (bst-leaf p) q = bst-leaf (≤A-trans q p)
bst-dec-lb (bst-node d L R p1 p2) q = bst-node d L R (≤A-trans q p1) p2

bst-inc-ub : ∀ {l' u' u : A} → bst l' u' → u' ≤A u ≡ tt → bst l' u
bst-inc-ub (bst-leaf p) q = bst-leaf (≤A-trans p q)
bst-inc-ub (bst-node d L R p1 p2) q = bst-node d L R p1 (≤A-trans p2 q)

bst-insert : ∀{l u : A}(d : A) → bst l u → bst (min l d) (max d u)
bst-insert{l}{u} d (bst-leaf p) = bst-inc-ub (bst-dec-lb (bst-leaf p) (min1-≤A {l} {d})) (max2-≤A {d} {u})
bst-insert d (bst-node d' L R p1 p2) with keep (d ≤A d') 
bst-insert d (bst-node d' L R p1 p2) | tt , p with bst-insert d L
bst-insert{l}{u} d (bst-node d' L R p1 p2) | tt , p | L' rewrite p = 
  bst-node d' L' (bst-inc-ub R (≤A-trans p2 max2-≤A)) (min1-mono p1) ≤A-refl
bst-insert d (bst-node d' L R p1 p2) | ff , p with bst-insert d R | ≤A-total p
bst-insert{l}{u} d (bst-node d' L R p1 p2) | ff , _ | R' | p rewrite p = 
  bst-node d' (bst-dec-lb L (≤A-trans min1-≤A p1)) R' ≤A-refl (max2-mono p2) 
