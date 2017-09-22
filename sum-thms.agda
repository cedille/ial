module sum-thms where

open import eq
open import sum
open import list
open import product
open import negation

inj₁-inj : ∀{ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}{x : A}{x'} → inj₁{ℓ}{ℓ'}{A}{B} x ≡ inj₁ x' → x ≡ x'
inj₁-inj refl = refl

¬∨ : ∀ {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
¬∨ (u , u') (inj₁ x) = u x
¬∨ (u , u') (inj₂ y) = u' y

¬Σ : ∀{A : Set}{B : A → Set} → (∀(x : A) → ¬ B x) → ¬ Σ A B
¬Σ p (a , b) = p a b

¬∧1 : ∀ {A B : Set} → ¬ A → ¬ (A ∧ B)
¬∧1 f (a , b) = f a

¬∧2 : ∀ {A B : Set} → ¬ B → ¬ (A ∧ B)
¬∧2 f (a , b) = f b

¬∀ : ∀{A : Set}{B : A → Set} → Σ A (λ x → ¬ B x) → ¬ ∀(x : A) → B x
¬∀ (a , b) f = b (f a) 
