module product-thms where

open import eq
open import level
open import product
open import functions

-- this is called the inspect idiom, in the Agda stdlib
keep : ∀{ℓ}{A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
keep x = ( x , refl )

eta-× : ∀{ℓ₁ ℓ₂ ℓ₃}{A : Set ℓ₁}{B : Set ℓ₂}{C : Set ℓ₃}{h : A × B → C}
  → (extensionality {ℓ₁ ⊔ ℓ₂}{ℓ₃})
  → (λ c → h (fst c , snd c)) ≡ h
eta-× {A = A}{B}{C}{h} ext = ext eta-×-aux
 where
   eta-×-aux : ∀{a : Σ A (λ x → B)} → h (fst a , snd a) ≡ h a
   eta-×-aux {(a , b)} = refl

eq-× : ∀{ℓ₁ ℓ₂}{A : Set ℓ₁}{B : Set ℓ₂}{a a' : A}{b b' : B}
  → a ≡ a'
  → b ≡ b'
  → (a , b) ≡ (a' , b')
eq-× refl refl = refl
