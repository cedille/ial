module nat-division-wf where

open import bool
open import bool-thms
open import eq
open import neq
open import nat
open import nat-thms
open import product
open import product-thms
open import sum
open import termination

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 10 _÷_!_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

{- a div-result for dividend x and divisor d consists of the quotient q, remainder r, and a proof that q * d + r = x -}
div-result : ℕ → ℕ → Set 
div-result x y = Σ ℕ (λ q → Σ ℕ (λ r → q * y + r ≡ x))

-- this uses well-founded induction.  The approach in nat-division.agda is simpler.
div-helper : ∀ (x : ℕ) → ↓𝔹 _>_ x → (y : ℕ) → y =ℕ 0 ≡ ff → div-result x y
div-helper x ↓x 0 () 
div-helper 0 (pf↓ fx) (suc y) _ = 0 , 0 , refl
div-helper (suc x) (pf↓ fx) (suc y) _ with keep (x < y) 
div-helper (suc x) (pf↓ fx) (suc y) _ | tt , p = 0 , suc x , refl
div-helper (suc x) (pf↓ fx) (suc y) _ | ff , p 
  with div-helper (x ∸ y) (fx (∸<1 {x} {y})) (suc y) refl
div-helper (suc x) (pf↓ fx) (suc y) _ | ff , p | q , r , u = 
  suc q , r , lem{q * suc y} (∸eq-swap{x}{y}{q * suc y + r} (<ff{x} p) u)
  where lem : ∀ {a b c : ℕ} → a + b + c ≡ x → suc (c + a + b) ≡ suc x 
        lem{a}{b}{c} p' rewrite +comm c a | sym (+assoc a c b) 
                              | +comm c b | +assoc a b c | p' = refl

_÷_!_ : (x : ℕ) → (y : ℕ) → y =ℕ 0 ≡ ff → div-result x y
x ÷ y ! p = div-helper x (↓-> x) y p

_÷_!!_ : ℕ → (y : ℕ) → y =ℕ 0 ≡ ff → ℕ × ℕ
x ÷ y !! p with x ÷ y ! p
... | q , r , p' = q , r

-- return quotient only
_÷_div_ : ℕ → (y : ℕ) → y =ℕ 0 ≡ ff → ℕ 
x ÷ y div p with x ÷ y ! p
... | q , r , p' = q

÷< : ∀ {d q r x : ℕ} → 1 < d ≡ tt → q * d + r ≡ suc x → q < suc x ≡ tt
÷<{0} () p
÷<{suc 0} () p
÷<{suc (suc d)}{0} u p = refl
÷<{suc (suc d)}{suc q}{r}{0} u ()
÷<{suc (suc d)}{suc q}{r}{suc x} u p with suc-inj{suc (d + q * suc (suc d) + r)}{suc x} p
... | p' rewrite sym (+suc (d + q * suc (suc d)) r) | +comm d (q * suc (suc d)) 
               | sym (+assoc (q * (suc (suc d))) d (suc r)) = ÷<{suc (suc d)}{q}{d + suc r}{x} refl p'  
