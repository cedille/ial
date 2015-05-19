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

{- Wf _<_ a means that the _<_ relation is well-founded below a.  That
   is, there are no infinite chains ... < a2 < a1 < a starting with a. -}
data Wf {ℓ ℓ'} {A : Set ℓ} (_<_ : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  pfWf : ∀ {x : A} → (∀ {y : A} → y < x → Wf _<_ y) → Wf _<_ x

WfBool : ∀ {ℓ}{A : Set ℓ} (_<_ : A → A → 𝔹) → A → Set ℓ 
WfBool{ℓ}{A} _<_ x = Wf{ℓ}{lzero} (λ (x y : A) → (x < y) ≡ tt) x

----------------------------------------------------------------------
-- theorems
----------------------------------------------------------------------

------------------------------
-- course of values on <
------------------------------
wf-< : ∀ (n : ℕ) → WfBool _<_ n
wf-< n = pfWf (lem n)
  where lem : ∀ x → ∀ {y} → y < x ≡ tt → WfBool _<_ y
        lem 0 {0} () 
        lem 0 {suc y} () 
        lem (suc x) {y} p with <-drop {y} p 
        ... | inj₁ u rewrite u = wf-< x
        ... | inj₂ u = lem x u


------------------------------
-- lexicographic combination
------------------------------
module lexcomb (ℓ ℓ' ℓ1 ℓ2 : level)(A : Set ℓ)(B : Set ℓ')(_<A_ : A → A → Set ℓ1)(_<B_ : B → B → Set ℓ2) where
  
  _<lex_ : A × B → A × B → Set (ℓ ⊔ ℓ1 ⊔ ℓ2)
  (a , b) <lex (a' , b') = a <A a' ∨ (a ≡ a' ∧ b <B b')

  {- If _<A_ is well-founded below a and if _<B_ is well-founded below every b, then
     _<lex_ is well-founded below (a , b) -}
  <lex-wf : {a : A} → Wf _<A_ a → ((b : B) → Wf _<B_ b) → {b : B} → Wf _<lex_ (a , b)
  <lex-wf {a} (pfWf fA) wB {b} = pfWf (helper (wB b))
     where helper : {b : B} → Wf _<B_ b → {y : A × B} → y <lex (a , b) → Wf _<lex_ y
           helper _ {a' , b'} (inj₁ u) = <lex-wf (fA u) wB
           helper (pfWf fB) {a' , b'} (inj₂ (u , u')) rewrite u = pfWf (helper (fB u'))

