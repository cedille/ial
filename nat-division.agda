module nat-division where

open import bool
open import bool-thms
open import eq
open import neq
open import nat
open import nat-thms
open import product
open import product-thms
open import sum

{- a div-result for dividend x and divisor d consists of the quotient q, remainder r, and a proof that q * d + r = x -}
div-result : ℕ → ℕ → Set 
div-result x d = Σ ℕ (λ q → Σ ℕ (λ r → q * d + r ≡ x ∧ r < d ≡ tt))

-- we use an upper bound n on the dividend x.  For an alternative approach, see nat-division-wf.agda.
divh : (n : ℕ) → (x : ℕ) → (y : ℕ) → x ≤ n ≡ tt → y =ℕ 0 ≡ ff → div-result x y
divh 0 0 0 p1 ()
divh 0 0 (suc y) p1 p2 = 0 , 0 , refl , refl
divh 0 (suc x) y () p2 
divh (suc n) x y p1 p2 with keep (x < y)
divh (suc n) x y p1 p2 | tt , pl = 0 , x , refl , pl
divh (suc n) x y p1 p2 | ff , pl with divh n (x ∸ y) y (∸≤2 n x y p1 p2) p2
divh (suc n) x y p1 p2 | ff , pl | q , r , pa , pb = suc q , r , lem{q}{r} pa , pb
  where lem : ∀{q r} → q * y + r ≡ x ∸ y → y + q * y + r ≡ x
        lem{q}{r} p rewrite sym (+assoc y (q * y) r) | p | +comm y (x ∸ y) = ∸+2{x}{y} (<ff{x}{y} pl)

-- the div-result contains the quotient, remainder, and proof relating them to the inputs
_÷_!_ : (x : ℕ) → (y : ℕ) → y =ℕ 0 ≡ ff → div-result x y 
x ÷ y ! p = divh x x y (≤-refl x) p 

-- return a pair of the quotient and remainder
_÷_!!_ : ℕ → (y : ℕ) → y =ℕ 0 ≡ ff → ℕ × ℕ
x ÷ y !! p with x ÷ y ! p
... | q , r , p' = q , r

-- return the quotient only
_÷_div_ : ℕ → (y : ℕ) → y =ℕ 0 ≡ ff → ℕ 
x ÷ y div p with x ÷ y ! p
... | q , r , p' = q

-- return the remainder only
_÷_mod_ : ℕ → (y : ℕ) → y =ℕ 0 ≡ ff → ℕ 
x ÷ y mod p with x ÷ y ! p
... | q , r , p' = r

data log-result (x : ℕ)(b : ℕ) : Set where
  pos-power : (e : ℕ) → (r : ℕ) → b pow e + r ≡ x → log-result x b
  no-power : x < b ≡ tt → log-result x b

{-
-- we use an upper bound n on x.  
logh : (n : ℕ) → (x : ℕ) → (b : ℕ) → x ≤ n ≡ tt → x =ℕ 0 ≡ ff → b =ℕ 0 ≡ ff → log-result x b
logh 0 0 y p1 () p3 
logh 0 (suc x) b () p2 p3
logh (suc n) (suc x) 0 _ _ ()
logh (suc n) 0 0 _ _ ()
logh (suc n) 0 (suc b) p1 () p3 
logh (suc n) (suc x) (suc b) p1 p2 p3 with (suc x) ÷ (suc b) ! p3
logh (suc n) (suc x) (suc b) p1 p2 p3 | 0 , r , pa , pb rewrite pa = no-power pb
logh (suc n) (suc x) (suc b) p1 p2 p3 | (suc q) , r , pa , pb 
  rewrite sym (suc-inj{b + q * (suc b) + r} pa) = {!  !}
{-
with logh n (suc q) (suc b) {!!} refl p3
logh (suc n) (suc x) (suc b) p1 p2 p3 | suc q , r , pa , pb | pos-power e r₁ x₁ = {!!}
logh (suc n) (suc x) (suc b) p1 p2 p3 | suc q , r , pa , pb | no-power x₁ = {!!}
-}
log : (x : ℕ) → (b : ℕ) → x =ℕ 0 ≡ ff → b =ℕ 0 ≡ ff → log-result x b
log x b p2 p3 = logh x x b (≤-refl x) p2 p3-}