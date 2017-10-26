open import bool
open import list
open import nat

_⇒_ : 𝕃 Set → Set → Set
[] ⇒ rettp = rettp
(x :: inputtps) ⇒ rettp = x → inputtps ⇒ rettp

_⇒𝕃_ : 𝕃 Set → Set → Set 
inputtps ⇒𝕃 rettp = (map 𝕃 inputtps) ⇒ (𝕃 rettp)

eatInputs : {inputtps : 𝕃 Set}{rettp : Set} → inputtps ⇒𝕃 rettp
eatInputs {[]} {rettp₁} = []
eatInputs {x₁ :: inputtps₁} {rettp₁} _ = eatInputs{inputtps₁}{rettp₁}

zipWith : {inputtps : 𝕃 Set}{rettp : Set} → (inputtps ⇒ rettp) → inputtps ⇒𝕃 rettp
zipWith {[]} {rettp} a = [ a ]
zipWith {tp :: inputtps} {rettp} f [] = eatInputs {inputtps}{rettp}
zipWith {tp :: inputtps} {rettp} f (h :: t) =
  helper{inputtps}{rettp} (f h) (zipWith{tp :: inputtps}{rettp} f t)
  where helper : {inputtps : 𝕃 Set}{rettp : Set} →
                 inputtps ⇒ rettp →
                 inputtps ⇒𝕃 rettp →
                 inputtps ⇒𝕃 rettp
        helper {[]} {rettp₁} f F = f :: F
        helper {tp :: inputtps} {rettp} _ _ [] = eatInputs{inputtps}{rettp}
        helper {tp :: inputtps} {rettp} f F (h :: t) = helper{inputtps}{rettp} (f h) (F t)

testTpList : 𝕃 Set
testTpList = (𝔹 :: ℕ :: ℕ :: [])

test = zipWith{testTpList}{ℕ} (λ b n m → if b then n else m) (tt :: tt :: ff :: []) (1 :: 2 :: 3 :: []) (10 :: 20 :: 30 :: 1000 :: [])
