module nat-division where

open import bool
open import bool-thms
open import eq
open import neq
open import nat
open import nat-thms
open import product
open import sum
open import well-founded

----------------------------------------------------------------------
-- syntax
----------------------------------------------------------------------

infixl 10 _÷_!_

----------------------------------------------------------------------
-- operations
----------------------------------------------------------------------

{- a div-result for dividend x and divisor d consists of the quotient q, remainder r, and a proof that q * d + r = x -}
div-result : ℕ → ℕ → Set 
div-result x d = Σ ℕ (λ q → Σ ℕ (λ r → q * d + r ≡ x))

div-helper : ∀ (x : ℕ) → WfStructBool _<_ x → (y : ℕ) → y =ℕ 0 ≡ ff → div-result x y
div-helper x wfx 0 () 
div-helper x (WfStep fx) (suc y) _ with 𝔹-dec (x =ℕ 0)
... | inj₁ u = 0 , 0 , sym (=ℕ-to-≡ u)
... | inj₂ u with 𝔹-dec (x < (suc y))
... | inj₁ v = 0 , (x , refl)
... | inj₂ v with (div-helper (x ∸ (suc y)) (fx (∸< {x} u)) (suc y) refl)
... | q , r , p with <ff {x} v 
... | p' with ∸eq-swap{x}{suc y}{q * (suc y) + r} p' p 
... | p'' = (suc q) , (r , lem p'')
   where lem : q * (suc y) + r + suc y ≡ x → suc (y + q * suc y + r) ≡ x
         lem p''' rewrite                        
                       +suc (q * (suc y) + r) y 
                     | +comm y (q * (suc y)) 
                     | +perm2 (q * (suc y)) r y = p'''

_÷_!_ : (x : ℕ) → (y : ℕ) → y =ℕ 0 ≡ ff → div-result x y
x ÷ y ! p = div-helper x (wf-< x) y p

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
