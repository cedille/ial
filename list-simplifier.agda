module list-simplifier where

open import bool
open import compose
open import eq
open import empty
open import level
open import list
open import list-thms
open import nat
open import neq
open import product
open import product-thms

data 𝕃term : Set → Set lone where
  _ʳ : {A : Set} → 𝕃 A → 𝕃term A
  _++ʳ_ : {A : Set} → 𝕃term A → 𝕃term A → 𝕃term A
  mapʳ : {A B : Set} → (A → B) → 𝕃term A → 𝕃term B
  _::ʳ_ : {A : Set} → A → 𝕃term A → 𝕃term A
  []ʳ : {A : Set} → 𝕃term A

𝕃⟦_⟧ : {A : Set} → 𝕃term A → 𝕃 A
𝕃⟦ l ʳ ⟧ = l
𝕃⟦ t1 ++ʳ t2 ⟧ = 𝕃⟦ t1 ⟧ ++ 𝕃⟦ t2 ⟧
𝕃⟦ mapʳ f t ⟧ = map f 𝕃⟦ t ⟧ 
𝕃⟦ x ::ʳ t ⟧ = x :: 𝕃⟦ t ⟧ 
𝕃⟦ []ʳ ⟧ = []

𝕃term-dev-step : {A : Set}(t : 𝕃term A) → 𝕃term A
𝕃term-dev-step ((t1a ++ʳ t1b) ++ʳ t2) = t1a ++ʳ (t1b ++ʳ t2) 
𝕃term-dev-step ((x ::ʳ t1) ++ʳ t2) = x ::ʳ (t1 ++ʳ t2) 
𝕃term-dev-step ([]ʳ ++ʳ t2) = t2 
𝕃term-dev-step ((l ʳ) ++ʳ t2) = ((l ʳ) ++ʳ t2)
𝕃term-dev-step ((mapʳ f t1) ++ʳ t2) = ((mapʳ f t1) ++ʳ t2)
𝕃term-dev-step (l ʳ) = l ʳ 
𝕃term-dev-step (mapʳ f (t1 ++ʳ t2)) = (mapʳ f t1) ++ʳ (mapʳ f t2) 
𝕃term-dev-step (mapʳ f (l ʳ)) = (map f l) ʳ 
𝕃term-dev-step (mapʳ f (mapʳ g t)) = mapʳ (f ∘ g) t 
𝕃term-dev-step (mapʳ f (x ::ʳ t)) = (f x) ::ʳ (mapʳ f t)
𝕃term-dev-step (mapʳ f []ʳ) = []ʳ 
𝕃term-dev-step (x ::ʳ t) = (x ::ʳ t)
𝕃term-dev-step []ʳ = []ʳ 

𝕃term-dev : {A : Set}(t : 𝕃term A) → 𝕃term A
𝕃term-dev (l ʳ) = (l ʳ)
𝕃term-dev (t1 ++ʳ t2) = 𝕃term-dev-step ((𝕃term-dev t1) ++ʳ (𝕃term-dev t2))
𝕃term-dev (mapʳ f t1) = 𝕃term-dev-step (mapʳ f (𝕃term-dev t1))
𝕃term-dev (x ::ʳ t1) = 𝕃term-dev-step (x ::ʳ (𝕃term-dev t1))
𝕃term-dev []ʳ = []ʳ 

𝕃term-devn : {A : Set}(t : 𝕃term A) → ℕ → 𝕃term A
𝕃term-devn t 0 = t
𝕃term-devn t (suc n) = 𝕃term-dev (𝕃term-devn t n)

𝕃term-dev-step-sound : {A : Set}(t : 𝕃term A) → 𝕃⟦ t ⟧ ≡ 𝕃⟦ 𝕃term-dev-step t ⟧
𝕃term-dev-step-sound ((t1a ++ʳ t1b) ++ʳ t2) = ++-assoc 𝕃⟦ t1a ⟧ 𝕃⟦ t1b ⟧ 𝕃⟦ t2 ⟧
𝕃term-dev-step-sound ((x ::ʳ t1) ++ʳ t2) = refl
𝕃term-dev-step-sound ([]ʳ ++ʳ t2) = refl
𝕃term-dev-step-sound ((l ʳ) ++ʳ t2) = refl
𝕃term-dev-step-sound ((mapʳ f t1) ++ʳ t2) = refl
𝕃term-dev-step-sound (l ʳ) = refl
𝕃term-dev-step-sound (mapʳ f (t1 ++ʳ t2)) = map-append f 𝕃⟦ t1 ⟧ 𝕃⟦ t2 ⟧
𝕃term-dev-step-sound (mapʳ f (l ʳ)) = refl
𝕃term-dev-step-sound (mapʳ f (mapʳ g t)) = map-compose f g 𝕃⟦ t ⟧
𝕃term-dev-step-sound (mapʳ f (x ::ʳ t)) = refl
𝕃term-dev-step-sound (mapʳ f []ʳ) = refl
𝕃term-dev-step-sound (x ::ʳ t) = refl
𝕃term-dev-step-sound []ʳ = refl

𝕃term-dev-sound : {A : Set}(t : 𝕃term A) → 𝕃⟦ t ⟧ ≡ 𝕃⟦ 𝕃term-dev t ⟧
𝕃term-dev-sound (l ʳ) = refl
𝕃term-dev-sound (t1 ++ʳ t2) 
  rewrite sym (𝕃term-dev-step-sound ((𝕃term-dev t1) ++ʳ (𝕃term-dev t2))) | 𝕃term-dev-sound t1 | 𝕃term-dev-sound t2 = refl
𝕃term-dev-sound (mapʳ f t1)
  rewrite sym (𝕃term-dev-step-sound (mapʳ f (𝕃term-dev t1))) | 𝕃term-dev-sound t1 = refl
𝕃term-dev-sound (x ::ʳ t1) rewrite 𝕃term-dev-sound t1 = refl
𝕃term-dev-sound []ʳ = refl

𝕃term-devn-sound : {A : Set}(t : 𝕃term A)(n : ℕ) → 𝕃⟦ t ⟧ ≡ 𝕃⟦ 𝕃term-devn t n ⟧
𝕃term-devn-sound t 0 = refl
𝕃term-devn-sound t (suc n) rewrite sym (𝕃term-dev-sound (𝕃term-devn t n)) = 𝕃term-devn-sound t n

module test1 {A B : Set}(f : A → B)(l1 l2 : 𝕃 A) where

  lhs = (mapʳ f (l1 ʳ)) ++ʳ (mapʳ f (l2 ʳ))

  rhs = mapʳ f ((l1 ʳ) ++ʳ (l2 ʳ))

  test-tp : Set
  test-tp = 𝕃⟦ lhs ⟧ ≡ 𝕃⟦ rhs ⟧

  test : test-tp
  test rewrite (𝕃term-dev-sound rhs) = refl

module test2 {A B : Set}(f : A → B)(l1 l2 l3 : 𝕃 A) where

  lhs = mapʳ f (((l1 ʳ) ++ʳ (l2 ʳ)) ++ʳ (l3 ʳ))

  rhs = 𝕃term-devn lhs 2

  test-tp : Set
  test-tp = 𝕃⟦ lhs ⟧ ≡ 𝕃⟦ rhs ⟧

  test : test-tp
  test rewrite (𝕃term-devn-sound lhs 2) = refl


{-
list-simplifier-test2 : ∀{A B : Set}(f : A → B)(l1 l2 l3 : 𝕃 A) → (map f l1 ++ map f l2) ++ map f l3 ≡ map f (l1 ++ l2 ++ l3)
list-simplifier-test2 f l1 l2 l3 
  rewrite 𝕃term-dev-sound (𝕃term-app (𝕃term-app (mapʳ f (𝕃term-list l1)) (mapʳ f (𝕃term-list l2)))
                            (mapʳ f (𝕃term-list l3))) 
  | 𝕃term-dev-sound (mapʳ f (𝕃term-app (𝕃term-list l1) (𝕃term-app (𝕃term-list l2) (𝕃term-list l3)))) 
  | 𝕃term-dev-sound (mapʳ f (𝕃term-app (𝕃term-list l2) (𝕃term-list l3))) = {!!}



{-with 
list-simplifier-test1 f l1 l2 l3 | t , p = {!!} -}-}