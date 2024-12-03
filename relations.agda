{- This file describes properties of computable relations. -}

open import bool
open import level
open import eq
open import product
open import product-thms
open import rel

module relations {A : Set} (_≥A_ : Rel A) where

reflexive : Set 
reflexive = ∀ {a : A} → a ≥A a 

transitive : Set
transitive = ∀ {a b c : A} → a ≥A b → b ≥A c → a ≥A c

preorder : Set 
preorder = reflexive ∧ transitive

_iso_ : Rel A
d iso d' = d ≥A d' ∧ d' ≥A d

iso-intro : ∀{x y : A} → x ≥A y → y ≥A x → x iso y 
iso-intro p1 p2 = p1 , p2

symmetric : Set 
symmetric = ∀{a b : A} → a ≥A b → b ≥A a

equivalence : Set 
equivalence = preorder ∧ symmetric

deterministic : Set
deterministic = ∀{a b c : A} → a ≥A b → a ≥A c → b ≡ c