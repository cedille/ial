{- The following code gives the basic idea of division by repeated
   subtraction.  We have to ask Agda not to check termination of this
   function, because it is not structurally terminating.  The versions
   in nat-division.agda and nat-division-wf.agda correct this problem,
   and can be judged by Agda to be terminating. -}

module nat-division-basic where

open import bool
open import eq
open import nat
open import product
open import sum

{-# NO_TERMINATION_CHECK #-}
div : (x y : ℕ) → y =ℕ 0 ≡ ff → ℕ × ℕ
div 0 _ _ = 0 , 0
div x y p with (x < y)
div x y p | tt = 0 , x 
div x y p | ff with div (x ∸ y) y p
div x y p | ff | q , r = suc q , r 

test-div : ℕ × ℕ
test-div = div 17 3 refl