module well-founded where

open import bool
open import eq
open import level
open import list
open import nat
open import nat-thms
open import product
open import sum

----------------------------------------------------------------------
-- types
----------------------------------------------------------------------

data WfStruct {ℓ ℓ'} {A : Set ℓ} (_<_ : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  WfStep : ∀ {x : A} → (∀ {y : A} → y < x → WfStruct _<_ y) → WfStruct _<_ x

WfStructBool : ∀ {ℓ}{A : Set ℓ} (_<_ : A → A → 𝔹) → A → Set ℓ 
WfStructBool{ℓ}{A} _<_ x = WfStruct{ℓ}{lzero} (λ (x y : A) → (x < y) ≡ tt) x

----------------------------------------------------------------------
-- theorems
----------------------------------------------------------------------

------------------------------
-- course of values on <
------------------------------
wf-< : ∀ (n : ℕ) → WfStructBool _<_ n
wf-< n = WfStep (lem n)
  where lem : ∀ x → ∀ {y} → y < x ≡ tt → WfStructBool _<_ y
        lem 0 {0} () 
        lem 0 {suc y} () 
        lem (suc x) {y} p with <-drop {y} p 
        ... | inj₁ u rewrite u = wf-< x
        ... | inj₂ u = lem x u


