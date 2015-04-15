module list-simplifier where

open import bool
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

data 𝕃term-app-view {A : Set} : 𝕃term A → Set lone where
  yes-𝕃term-app : ∀{t1 t2 : 𝕃term A} → 𝕃term-app-view (𝕃term-app t1 t2)
  no-𝕃term-app : ∀{t : 𝕃term A} → (∀{t1 t2 : 𝕃term A} → t ≢ 𝕃term-app t1 t2) → 𝕃term-app-view t

get-𝕃term-app-view : ∀{A : Set} → (t : 𝕃term A) → 𝕃term-app-view t
get-𝕃term-app-view (𝕃term-app t1 t2) = yes-𝕃term-app 
get-𝕃term-app-view (𝕃term-list _) = no-𝕃term-app (λ ())
get-𝕃term-app-view (𝕃term-map _ _) = no-𝕃term-app (λ ())
get-𝕃term-app-view (𝕃term-cons _ _) = no-𝕃term-app (λ ())
get-𝕃term-app-view 𝕃term-nil = no-𝕃term-app (λ ())

𝕃term⟦_⟧ : {A : Set} → 𝕃term A → 𝕃 A
𝕃term⟦ 𝕃term-list l ⟧ = l
𝕃term⟦ 𝕃term-app t1 t2 ⟧ = 𝕃term⟦ t1 ⟧ ++ 𝕃term⟦ t2 ⟧
𝕃term⟦ 𝕃term-map f t ⟧ = map f 𝕃term⟦ t ⟧ 
𝕃term⟦ 𝕃term-cons x t ⟧ = x :: 𝕃term⟦ t ⟧ 
𝕃term⟦ 𝕃term-nil ⟧ = []

𝕃term-step-app : {A : Set} → (t1 t2 : 𝕃term A) → 𝕃term-app-view t1 → 𝕃term A
𝕃term-step-app t1 t2 (no-𝕃term-app p) = 𝕃term-app t1 t2
𝕃term-step-app (𝕃term-app t1a t1b) t2 yes-𝕃term-app = 𝕃term-app t1a (𝕃term-app t1b t2)

𝕃term-step : {A : Set} → 𝕃term A → 𝕃term A
𝕃term-step (𝕃term-app t1 t2) with get-𝕃term-app-view t1
𝕃term-step (𝕃term-app t1 t2) | no-𝕃term-app p = 𝕃term-app t1 t2
𝕃term-step (𝕃term-app (𝕃term-app t1a t1b) t2) | yes-𝕃term-app = 𝕃term-app t1a (𝕃term-app t1b t2)
𝕃term-step (𝕃term-list l) = 𝕃term-list l
𝕃term-step (𝕃term-map f t) = 𝕃term-map f t
𝕃term-step (𝕃term-cons x t) = 𝕃term-cons x t
𝕃term-step 𝕃term-nil = 𝕃term-nil

𝕃term-step-sound : {A : Set}(t : 𝕃term A) → 𝕃term⟦ t ⟧ ≡ 𝕃term⟦ 𝕃term-step t ⟧
𝕃term-step-sound (𝕃term-app t1 t2) with get-𝕃term-app-view t1 
𝕃term-step-sound (𝕃term-app t1 t2) | no-𝕃term-app q = refl
𝕃term-step-sound (𝕃term-app (𝕃term-app t1a t1b) t2) | yes-𝕃term-app rewrite ++-assoc 𝕃term⟦ t1a ⟧ 𝕃term⟦ t1b ⟧ 𝕃term⟦ t2 ⟧ = refl
𝕃term-step-sound (𝕃term-list l) = refl
𝕃term-step-sound (𝕃term-map f t) = refl
𝕃term-step-sound (𝕃term-cons x t) = refl
𝕃term-step-sound (𝕃term-nil) = refl
