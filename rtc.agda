{- reflexive transitive closure of a relation -}
open import rel
open import relations 
open import bool
open import list
open import list-thms
import bool-relations

module rtc where

data _⋆ {A : Set} (r : Rel A) : Rel A where
  ⋆refl : ∀{a : A} → (r ⋆) a a
  ⋆base_ : ∀{a a' : A} → r a a' → (r ⋆) a a'
  _⋆trans_ : ∀{a a' a'' : A} → (r ⋆) a a' → (r ⋆) a' a'' → (r ⋆) a a''

infix 10 _⋆
infixl 10 _⋆trans_
infixl 11 ⋆base_

-- reflexive-transitive closure preserves symmetry
⋆symm : ∀{A : Set}{r : Rel A} → symmetric r → symmetric (r ⋆)
⋆symm u (⋆base x) = ⋆base (u x)
⋆symm u ⋆refl = ⋆refl
⋆symm u (p ⋆trans p₁) = (⋆symm u p₁) ⋆trans (⋆symm u p)

⋆mono : ∀{A : Set}{r1 r2 : Rel A} → r1 ⊆ r2 → r1 ⋆ ⊆ r2 ⋆
⋆mono u (⋆base p) = ⋆base (u p)
⋆mono u ⋆refl = ⋆refl
⋆mono u (r1 ⋆trans r2) = (⋆mono u r1) ⋆trans (⋆mono u r2)

⋆idem : ∀{A : Set}{r : Rel A} → r ⋆ ⋆ ⊆ r ⋆
⋆idem (⋆base p) = p
⋆idem ⋆refl = ⋆refl
⋆idem (p1 ⋆trans p2) = (⋆idem p1) ⋆trans (⋆idem p2)

preserves-⋆ : ∀{A B : Set}{eq : B → B → 𝔹}{f : A → 𝕃 B}
               {r : Rel A} →
               bool-relations.computational-equality eq → 
               bool-relations.reflexive eq → 
               preserves-set r f eq →
               preserves-set (r ⋆) f eq
preserves-⋆ {A}{B} {eq} {f} {r} ceq rf p {x} ⋆refl = isSublist-refl{B}{eq} rf {f x}
preserves-⋆ {A}{B} {eq} {f} {r} ceq rf p (⋆base x) = p x
preserves-⋆ {A}{B} {eq} {f} {r} ceq rf p (_⋆trans_{x}{y}{z} u1 u2) =
  isSublist-trans {B} {eq} {f z} {f y} {f x} ceq
    (preserves-⋆{A}{B}{eq}{f}{r} ceq rf p u2)
    (preserves-⋆{A}{B}{eq}{f}{r} ceq rf p u1)