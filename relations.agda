{- This file describes properties of relations. -}

open import bool
open import level
open import eq
open import list
open import product
open import product-thms
open import rel

module relations {ℓ : level} {A : Set ℓ} (_≥A_ : Rel A) where

reflexive : Set ℓ
reflexive = ∀ {a : A} → a ≥A a 

transitive : Set ℓ
transitive = ∀ {a b c : A} → a ≥A b → b ≥A c → a ≥A c

preorder : Set ℓ
preorder = reflexive ∧ transitive

_iso_ : Rel A
d iso d' = d ≥A d' ∧ d' ≥A d

iso-intro : ∀{x y : A} → x ≥A y → y ≥A x → x iso y 
iso-intro p1 p2 = p1 , p2

symmetric : Set ℓ
symmetric = ∀{a b : A} → a ≥A b → b ≥A a

equivalence : Set ℓ
equivalence = preorder ∧ symmetric

deterministic : Set ℓ
deterministic = ∀{a b c : A} → a ≥A b → a ≥A c → b ≡ c

preserves-set : ∀{B : Set} → (f : A → 𝕃 B) → (eq : B → B → 𝔹) → Set ℓ
preserves-set f eq = ∀{a b : A} → a ≥A b → isSublist (f b) (f a) eq ≡ tt