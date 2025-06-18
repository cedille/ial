open import level
open import eq
open import product
open import sum

module rel where

Rel : {ℓ : level} → Set ℓ → Set (lsuc ℓ)
Rel{ℓ} A = A → A → Set ℓ

_⟨_⟩_ : ∀ {A : Set} → A → Rel A → A → Set
a ⟨ r ⟩ a' = r a a'

_∪_ : ∀ {A : Set} → Rel A → Rel A → Rel A
(r ∪ r') x y = (r x y) ∨ (r' x y)

_∩_ : ∀ {A : Set} → Rel A → Rel A → Rel A
(r ∩ r') x y = (r x y) ∧ (r' x y)

1r : ∀ {A : Set} → Rel A
1r = _≡_

_∘_ : ∀ {A : Set} → Rel A → Rel A → Rel A
_∘_ {A} _r_ _r'_ x z = Σ[ y ∈ A ] ((x r y) ∧ (y r' z))

infixr 10 _∘_
infixr 9 _∪_

_⊆_ : ∀{A : Set} → Rel A → Rel A → Set
R ⊆ S = ∀ {a}{a'} → R a a' → S a a'

infix 8 _⊆_
