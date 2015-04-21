open import bool
open import eq
open import product
open import product-thms

module relations (A : Set) (_≤A_ : A → A → 𝔹) where

total : Set
total = ∀ {a b : A} → a ≤A b ≡ ff → b ≤A a ≡ tt

transitive : Set
transitive = ∀ {a b c : A} → a ≤A b ≡ tt → b ≤A c ≡ tt → a ≤A c ≡ tt

reflexive : Set
reflexive = ∀ {a : A} → a ≤A a ≡ tt

total-reflexive : total → reflexive
total-reflexive tot {a} with keep (a ≤A a)
total-reflexive tot {a} | tt , p = p
total-reflexive tot {a} | ff , p = tot p

_iso_ : A → A → 𝔹
d iso d' = d ≤A d' && d' ≤A d

iso-intro : ∀{x y : A} → x ≤A y ≡ tt → y ≤A x ≡ tt → x iso y ≡ tt
iso-intro p1 p2 rewrite p1 | p2 = refl


