{- This file describes properties of computable relations. -}

open import bool
open import bool-thms2
open import level
open import eq
open import product
open import product-thms

module bool-relations {ℓ : level}{A : Set ℓ} (_≤A_ : A → A → 𝔹) where

reflexive : Set ℓ
reflexive = ∀ {a : A} → a ≤A a ≡ tt

transitive : Set ℓ
transitive = ∀ {a b c : A} → a ≤A b ≡ tt → b ≤A c ≡ tt → a ≤A c ≡ tt

preorder : Set ℓ
preorder = reflexive ∧ transitive

total : Set ℓ
total = ∀ {a b : A} → a ≤A b ≡ ff → b ≤A a ≡ tt

total-reflexive : total → reflexive 
total-reflexive tot {a} with keep (a ≤A a)
total-reflexive tot {a} | tt , p = p
total-reflexive tot {a} | ff , p = tot p

_iso𝔹_ : A → A → 𝔹
d iso𝔹 d' = d ≤A d' && d' ≤A d

iso𝔹-intro : ∀{x y : A} → x ≤A y ≡ tt → y ≤A x ≡ tt → x iso𝔹 y ≡ tt
iso𝔹-intro p1 p2 rewrite p1 | p2 = refl

symmetric : Set ℓ
symmetric = ∀{a b : A} → a ≤A b ≡ tt → b ≤A a ≡ tt

equivalence : Set ℓ
equivalence = preorder ∧ symmetric

~symmetric : symmetric → ∀{a b : A} → a ≤A b ≡ ff → b ≤A a ≡ ff
~symmetric symm {a}{b} p with keep (b ≤A a)
~symmetric symm {_} {_} p | tt , p' rewrite symm p' with p 
~symmetric symm {_} {_} p | tt , p' | ()
~symmetric symm {_} {_} p | ff , p' = p'

~symmetric2 : symmetric → ∀{a b : A} → ~ (a ≤A b) ≡ tt → ~ (b ≤A a) ≡ tt
~symmetric2 symm {a}{b} p rewrite ~symmetric symm{a}{b} (~-≡-tt p) = refl

computational-equality : Set ℓ
computational-equality = ∀{x y : A} → x ≤A y ≡ tt → x ≡ y