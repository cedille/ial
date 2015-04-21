module list-simplifier where

open import bool
open import compose
open import eq
open import empty
open import level
open import list
open import list-thms
open import neq
open import product
open import product-thms

data 𝕃term : Set → Set lone where
  𝕃term-list : {A : Set} → 𝕃 A → 𝕃term A
  𝕃term-app : {A : Set} → 𝕃term A → 𝕃term A → 𝕃term A
  𝕃term-map : {A B : Set} → (A → B) → 𝕃term A → 𝕃term B
  𝕃term-cons : {A : Set} → A → 𝕃term A → 𝕃term A
  𝕃term-nil : {A : Set} → 𝕃term A

𝕃term⟦_⟧ : {A : Set} → 𝕃term A → 𝕃 A
𝕃term⟦ 𝕃term-list l ⟧ = l
𝕃term⟦ 𝕃term-app t1 t2 ⟧ = 𝕃term⟦ t1 ⟧ ++ 𝕃term⟦ t2 ⟧
𝕃term⟦ 𝕃term-map f t ⟧ = map f 𝕃term⟦ t ⟧ 
𝕃term⟦ 𝕃term-cons x t ⟧ = x :: 𝕃term⟦ t ⟧ 
𝕃term⟦ 𝕃term-nil ⟧ = []

𝕃term-dev-step : {A : Set}(t : 𝕃term A) → 𝕃term A
𝕃term-dev-step (𝕃term-app (𝕃term-app t1a t1b) t2) = 𝕃term-app t1a (𝕃term-app t1b t2) 
𝕃term-dev-step (𝕃term-app (𝕃term-cons x t1) t2) = 𝕃term-cons x (𝕃term-app t1 t2) 
𝕃term-dev-step (𝕃term-app 𝕃term-nil t2) = t2 
𝕃term-dev-step (𝕃term-app (𝕃term-list l) t2) = 𝕃term-app (𝕃term-list l) t2
𝕃term-dev-step (𝕃term-app (𝕃term-map f t1) t2) = 𝕃term-app (𝕃term-map f t1) t2
𝕃term-dev-step (𝕃term-list l) = 𝕃term-list l 
𝕃term-dev-step (𝕃term-map f (𝕃term-app t1 t2)) = 𝕃term-app (𝕃term-map f t1) (𝕃term-map f t2) 
𝕃term-dev-step (𝕃term-map f (𝕃term-list l)) = 𝕃term-list (map f l) 
𝕃term-dev-step (𝕃term-map f (𝕃term-map g t)) = 𝕃term-map (f ∘ g) t 
𝕃term-dev-step (𝕃term-map f (𝕃term-cons x t)) = 𝕃term-cons (f x) (𝕃term-map f t)
𝕃term-dev-step (𝕃term-map f 𝕃term-nil) = 𝕃term-nil 
𝕃term-dev-step (𝕃term-cons x t) = 𝕃term-cons x t 
𝕃term-dev-step 𝕃term-nil = 𝕃term-nil 

𝕃term-dev : {A : Set}(t : 𝕃term A) → 𝕃term A
𝕃term-dev (𝕃term-list l) = 𝕃term-list l 
𝕃term-dev (𝕃term-app t1 t2) = 𝕃term-dev-step (𝕃term-app (𝕃term-dev t1) (𝕃term-dev t2))
𝕃term-dev (𝕃term-map f t1) = 𝕃term-dev-step (𝕃term-map f (𝕃term-dev t1))
𝕃term-dev (𝕃term-cons x t1) = 𝕃term-dev-step (𝕃term-cons x (𝕃term-dev t1))
𝕃term-dev 𝕃term-nil = 𝕃term-nil 

𝕃term-dev-step-sound : {A : Set}(t : 𝕃term A) → 𝕃term⟦ t ⟧ ≡ 𝕃term⟦ 𝕃term-dev-step t ⟧
𝕃term-dev-step-sound (𝕃term-app (𝕃term-app t1a t1b) t2) = ++-assoc 𝕃term⟦ t1a ⟧ 𝕃term⟦ t1b ⟧ 𝕃term⟦ t2 ⟧
𝕃term-dev-step-sound (𝕃term-app (𝕃term-cons x t1) t2) = refl
𝕃term-dev-step-sound (𝕃term-app 𝕃term-nil t2) = refl
𝕃term-dev-step-sound (𝕃term-app (𝕃term-list l) t2) = refl
𝕃term-dev-step-sound (𝕃term-app (𝕃term-map f t1) t2) = refl
𝕃term-dev-step-sound (𝕃term-list l) = refl
𝕃term-dev-step-sound (𝕃term-map f (𝕃term-app t1 t2)) = map-append f 𝕃term⟦ t1 ⟧ 𝕃term⟦ t2 ⟧
𝕃term-dev-step-sound (𝕃term-map f (𝕃term-list l)) = refl
𝕃term-dev-step-sound (𝕃term-map f (𝕃term-map g t)) = map-compose f g 𝕃term⟦ t ⟧
𝕃term-dev-step-sound (𝕃term-map f (𝕃term-cons x t)) = refl
𝕃term-dev-step-sound (𝕃term-map f 𝕃term-nil) = refl
𝕃term-dev-step-sound (𝕃term-cons x t) = refl
𝕃term-dev-step-sound 𝕃term-nil = refl

𝕃term-dev-sound : {A : Set}(t : 𝕃term A) → 𝕃term⟦ t ⟧ ≡ 𝕃term⟦ 𝕃term-dev t ⟧
𝕃term-dev-sound (𝕃term-list l) = refl
𝕃term-dev-sound (𝕃term-app t1 t2) 
  rewrite sym (𝕃term-dev-step-sound (𝕃term-app (𝕃term-dev t1) (𝕃term-dev t2))) | 𝕃term-dev-sound t1 | 𝕃term-dev-sound t2 = refl
𝕃term-dev-sound (𝕃term-map f t1)
  rewrite sym (𝕃term-dev-step-sound (𝕃term-map f (𝕃term-dev t1))) | 𝕃term-dev-sound t1 = refl
𝕃term-dev-sound (𝕃term-cons x t1) rewrite 𝕃term-dev-sound t1 = refl
𝕃term-dev-sound 𝕃term-nil = refl

list-simplifier-test1 : ∀{A B : Set}(f : A → B)(l1 l2 : 𝕃 A) → (map f l1 ++ map f l2) ≡ map f (l1 ++ l2)
list-simplifier-test1 f l1 l2 = sym (𝕃term-dev-sound (𝕃term-map f (𝕃term-app (𝕃term-list l1) (𝕃term-list l2))))

list-simplifier-test2 : ∀{A B : Set}(f : A → B)(l1 l2 l3 : 𝕃 A) → (map f l1 ++ map f l2) ++ map f l3 ≡ map f (l1 ++ l2 ++ l3)
list-simplifier-test2 f l1 l2 l3 
  rewrite 𝕃term-dev-sound (𝕃term-app (𝕃term-app (𝕃term-map f (𝕃term-list l1)) (𝕃term-map f (𝕃term-list l2)))
                            (𝕃term-map f (𝕃term-list l3))) 
  | 𝕃term-dev-sound (𝕃term-map f (𝕃term-app (𝕃term-list l1) (𝕃term-app (𝕃term-list l2) (𝕃term-list l3)))) 
  | 𝕃term-dev-sound (𝕃term-map f (𝕃term-app (𝕃term-list l2) (𝕃term-list l3))) = {!!}



{-with 
list-simplifier-test1 f l1 l2 l3 | t , p = {!!} -}