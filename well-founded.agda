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

{- Wf _>_ a means that the _>_ relation is well-founded below a.  That
   is, there are no infinite chains a > a1 > ... starting with a. 
   One can also say that _>_ terminates from a. -}
data Wf {ℓ ℓ'} {A : Set ℓ} (_>_ : A → A → Set ℓ') : A → Set (ℓ ⊔ ℓ') where
  pfWf : ∀ {x : A} → (∀ {y : A} → x > y → Wf _>_ y) → Wf _>_ x

Wf𝔹 : ∀ {ℓ}{A : Set ℓ} (_>_ : A → A → 𝔹) → A → Set ℓ 
Wf𝔹{ℓ}{A} _>_ x = Wf{ℓ}{lzero} (λ (x y : A) → (x > y) ≡ tt) x

----------------------------------------------------------------------
-- theorems
----------------------------------------------------------------------

------------------------------
-- course of values on >
------------------------------
wf-> : ∀ (n : ℕ) → Wf𝔹 _>_ n
wf-> n = pfWf (lem n)
  where lem : ∀ y → ∀ {x} → y > x ≡ tt → Wf𝔹 _>_ x
        lem 0 {0} () 
        lem 0 {suc y} () 
        lem (suc x) {y} p with <-drop {y} p 
        ... | inj₁ u rewrite u = wf-> x
        ... | inj₂ u = lem x u


------------------------------
-- lexicographic combination
------------------------------
module lexcomb {ℓ ℓ' ℓ1 ℓ2 : level}{A : Set ℓ}{B : Set ℓ'}(_>A_ : A → A → Set ℓ1)(_>B_ : B → B → Set ℓ2) where
  
  _>lex_ : A × B → A × B → Set (ℓ ⊔ ℓ1 ⊔ ℓ2)
  (a , b) >lex (a' , b') = a >A a' ∨ (a ≡ a' ∧ b >B b')

  {- If _>A_ is well-founded below a and if _>B_ is well-founded below every b, then
     _>lex_ is well-founded below (a , b) -}
  >lex-wf : {a : A} → Wf _>A_ a → ((b : B) → Wf _>B_ b) → {b : B} → Wf _>lex_ (a , b)
  >lex-wf {a} (pfWf fA) wB {b} = pfWf (helper fA (wB b))
     where helper : {a : A} → (∀{y : A} → a >A y → Wf _>A_ y) → {b : B} → Wf _>B_ b → {y : A × B} → (a , b) >lex y → Wf _>lex_ y
           helper fA _ {a' , b'} (inj₁ u) = >lex-wf (fA u) wB
           helper fA (pfWf fB) {a' , b'} (inj₂ (u , u')) rewrite u = pfWf (helper fA (fB u'))

------------------------------
-- measure functions
------------------------------

{- Suppose we want to prove that _>A_ is terminating starting from a, and we have a function m, 
   called a measure function, that maps A to another type B, where we know an 
   ordering _>B_ is terminating starting from (m a).

   Then as long as m is preserved by _>A_ -- meaning that a >A a' implies m a >B m a' -- then we
   can derive termination starting from a from termination starting from b. -}
module measure {ℓ ℓ' ℓ1 ℓ2 : level}{A : Set ℓ}{B : Set ℓ'}(_>A_ : A → A → Set ℓ1)(_>B_ : B → B → Set ℓ2)
               (m : A → B)
               (preservem : ∀{a a' : A} → a >A a' → m a >B m a') where

  measure-> : ∀ {a : A} → Wf _>B_ (m a) → Wf _>A_ a
  measure->{a} (pfWf fM) = pfWf h
    where h : {y : A} → a >A y → Wf _>A_ y
          h{y} p = measure-> (fM (preservem p))