module termination-examples where

open import empty
open import eq
open import level
open import negation
open import rel
open import relations
open import termination

-- reflexive relations diverge
refl-¬↓ : ∀{A : Set}{R : Rel A} →
          reflexive R →
          ∀{a : A} →
          ¬ (↓ R a)
refl-¬↓ {A} {R} rfl {a} (pf↓ f) = refl-¬↓{A}{R} rfl (f (rfl {a}))